structure Intermediate =
struct
	open Ast

	type label = int
	type symbol = Symbol.symbol

	datatype store = Reg of int
	               | Label of int
				   | IntImm of int

	val rc = ref 0
	val lc = ref 0

	val env = ref [] : (int * store) list ref

	fun lookup' i = List.find (fn (m,_) => i = m) (!env) 

	fun lookup s = (fn NONE => NONE | (SOME (x,y)) => SOME y) 
						(lookup' (Symbol.hash s))

	fun insert s r = env := (Symbol.hash s,r) :: !env

	fun register () = Reg (rc := !rc + 1; !rc)
	fun label () = Label (lc := !lc + 1; !lc)

	datatype ir =
		ADD of store * store * store
	  |	ADDI of store * store * int
	  |	AND of store * store * store 
	  |	ANDI of store * store * int
	  |	SUB of store * store * store
	  |	SUBI of store * store * int
	  | DIV of store * store * store
	  | DIVI of store * store * int
	  |	BRZ of label
	  |	BRNZ of label
	  |	MUL of store * store * store
	  |	MULI of store * store * int
	  |	MOV of store * store
	  |	LABEL of label
	  | LIT_INT of int
	  | RET of store
	  | FUNCTION of store * Ast.ty * (store * Ast.ty) list * ir list
	  | UnconvertedExp of Ast.exp

	fun trans_e (BinOp {opr=p,lhs,rhs,...}) =
		let 
			val (r1,i1) = trans_e lhs
			val (r2,i2) = trans_e rhs
			val r3 = register ()
			val cn = 
				(case p of Plus => [ADD (r3, r1, r2)]
			             | Minus => [SUB (r3, r1, r2)]
						 | Times => [MUL (r3, r1, r2)]
						 | Div => [DIV (r3, r1, r2)]
						 | Equal => [AND (r3, r1, r2)]
						 | _ => raise Fail "Unhandled binop")
		in
			(r3, i1 @ i2 @ cn)
		end
	  | trans_e (Var {name,symtab,...}) =
	  	let
			val r = case lookup name of NONE => 
						let
							val r' = register ()
							val _ = insert name r'
						in
							r'
						end
					   | (SOME x) => x
		in
			(r,[])
		end
	  | trans_e (Fn {attr,match,symtab}) =
	  	let
			val f = hd match (* FIXME process more than one clause *)
			val fname = label ()
			val ty = Types.tyInt
			val pat = (case (#1 f) of
						VarPat {attr,name,symtab} => let
							val r = register ()
							val _ = insert name r
						in
							[(r,Types.tyInt)]
						end
						| _ => raise Fail "Unhandled pat in codegen")
			val (ret,body) = trans_e (#2 f)
			val body' = body @ [RET ret]
		in
			(fname, [FUNCTION (fname,ty,pat,body')])
		end
	  | trans_e (Int i) =
	  	let
			val r = register ()
		in
			(r, [ADD (r,IntImm 0,IntImm i)])
		end
	  | trans_e x = (register(), [UnconvertedExp x])

	fun emit_r (Reg i) = "%r" ^ Int.toString i
	  | emit_r (Label i) = "@anon_" ^ Int.toString i
	  | emit_r (IntImm i) = Int.toString i

	fun emit_ty x = "i32"

	fun fmt instr ty (a,b,c) =
		emit_r a ^ " = " ^ 
				   instr ^ 
				   	 " " ^ 
			  emit_ty ty ^ 
			         " " ^
				emit_r b ^
				     "," ^
			    emit_r c 

	fun emit' (ADD ops) = fmt "add" "i32" ops 
	  | emit' (SUB ops) = fmt "sub" "i32" ops
	  | emit' (MUL ops) = fmt "mul" "i32" ops
	  | emit' (AND ops) = fmt "and" "i32" ops
	  | emit' (RET r) = "ret " ^ emit_r r
	  | emit' (FUNCTION (n,rt,args,body)) = 
	  	"define fastcc " ^ emit_ty rt ^ " " ^
		emit_r n ^ "(" ^
		(String.concatWith "," 
			(map (fn (x,t) => emit_ty t ^ " " ^ emit_r x) args)) ^
		") {\n\t\tentry:\n\t\t" ^ 
		(String.concatWith "\n\t\t" (map emit' body)) ^
		"\n\t}"
	  | emit' _ = "# unemitted"

	fun emit [] = "\n"
	  | emit (h::t) = "\t" ^ emit' h ^ "\n"

	fun translate symtab =
		let
			val {venv,tenv} = !symtab

			val vkeys = Symbol.keys (!venv)
		in
			List.foldl (fn ((s,(t,SOME e)),instr) =>
				let
					val (r,i) = trans_e e
				in
					i @ instr
				end
				| _ => []) [] vkeys
		end
end

