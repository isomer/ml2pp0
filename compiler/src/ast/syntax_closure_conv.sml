structure SyntaxClosureConv : SYNTAX_PASS =
struct
structure A = Ast

fun id x = x

fun union l r = ListMergeSort.uniqueSort String.compare (l@r)
fun union_all (l:(string list list)):(string list) = 
	let
		val flatlist:(string list) = foldl (op @) [] l
	in
		ListMergeSort.uniqueSort String.compare flatlist
	end

fun set_difference [] [] = []
  | set_difference l  [] = l
  | set_difference [] r  = []
  | set_difference (lh::lt) (rh::rt) = 
  	if lh = rh then set_difference lt rt
	else if lh < rh then (lh::(set_difference lt (rh::rt)))
	else if lh > rh then (set_difference (lh::lt) rt)
	else raise Fail "Can't happen"

fun enumerate_variables_astnode (A.Op var) = [Symbol.toString var]
  | enumerate_variables_astnode (A.Var var) = [Symbol.toString var]
  | enumerate_variables_astnode (A.VarPat var) = [Symbol.toString var]
  | enumerate_variables_astnode (A.OpPat var) = [Symbol.toString var]
  | enumerate_variables_astnode x = []

fun is_builtin symtab symname = 
	(case Symtab.lookup_v symtab (Symbol.fromString symname) of
		(_, SOME (A.Node (A.BuiltIn _,_,_,_))) => true
		| (_, _) => false
	) handle _ => false

fun enumerate_variables_ast (A.Node (A.Match,tyo,symtab,[pat,exp]))
 	= set_difference (enumerate_variables_ast exp) (enumerate_variables_ast pat)
  | enumerate_variables_ast (A.Node (ast,tyo,symtab,children) )
	= (union_all ((enumerate_variables_astnode ast)::(map enumerate_variables_ast children)))

fun enumerate_filtered_variables_ast (node as (A.Node (_,_,symtab,_))) = 
	List.filter (fn symname => not (is_builtin symtab symname)) (enumerate_variables_ast node)

fun repr l = "["^(String.concatWith "," l)^"]"

fun insert_new_argument arg (A.Node (A.Match,ty,symtab,children)) =
	let
		val args=(map (fn x=>A.Node (A.VarPat (Symbol.fromString x),ty,symtab,[])) arg)
	in 
		(A.Node (A.Match,ty,symtab,
			[A.Node (A.Tuple,ty,symtab,args@[hd children])]@(tl children)))
	end
  | insert_new_argument arg x = x

fun string_to_var ty symtab name =
	A.Node (A.Var (Symbol.fromString name), ty, symtab, [])

fun closure_conv_exp (node as (A.Node (A.Fn,ty,symtab,children))) = 
	let
		val exps = (union_all (map enumerate_filtered_variables_ast children))
		val vars:A.ast list = (map (string_to_var ty symtab) exps)
(*		val _ = print ((PrettyPrint.ppexp node)^ "=" ^ repr exps ^ "\n") *)
		val ret = (A.Node (A.Fn,ty,symtab,
			map (fn x=>insert_new_argument exps x) children ))
(*		val _ = print ((PrettyPrint.ppexp node)^ " => " ^ (PrettyPrint.ppexp ret) ^ "\n") *)
	in
		(A.Node (A.App,ty,symtab,ret :: vars))
	end
  | closure_conv_exp x = x

type syntax_pass_param = unit

fun translate _ prog = (AstOps.ast_map_symtab {
		decfun = id,
		expfun = closure_conv_exp,
		bindfun = id,
		tyfun = id,
		oprfun = id,
		clausesfun = id,
		clausefun = id
		} Symtab.top_level; prog)
end
