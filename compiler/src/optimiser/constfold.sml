structure ConstFold =
struct

structure A = Ast

fun id a = a

(* has no sideeffects? *)
fun is_pure node = true

(* Check for identity functions *)
fun id_func (node as (A.BinOp {attr,opr,lhs,rhs})) = 
	if (MathRules.is_id_func_lhs opr lhs rhs) then rhs
	else if (MathRules.is_id_func_rhs opr lhs rhs) then lhs
	else if (MathRules.is_commutative opr) andalso (MathRules.is_id_func_lhs opr rhs lhs) then lhs
	else if (MathRules.is_commutative opr) andalso (MathRules.is_id_func_rhs opr rhs lhs) then rhs
	else node
  | id_func node = node

(* commute's a node *)
fun commute_node (A.BinOp {attr,opr,lhs,rhs}) = (A.BinOp {attr=attr,opr=opr,lhs=rhs,rhs=lhs})
  | commute_node _ = raise Fail "Can only commute BinOps"

(* returns true if lhs == rhs *)
fun equivilent_ast lhs rhs = (PrettyPrint.ppexp lhs) = (PrettyPrint.ppexp rhs)

(* Special forms 
 * This is for things like the "Zero property of multiplication"
 * This may be run twice for commutivity
*)
fun special_fold_const (A.BinOp {opr=A.Times,lhs,rhs=A.Int 0,...}) = A.Int 0
  | special_fold_const (A.BinOp {opr=A.BAnd,lhs,rhs=A.Bool false,...}) = A.Bool false
  | special_fold_const (A.BinOp {opr=A.BOr,lhs,rhs=A.Bool true,...}) = A.Bool true
  | special_fold_const node = node

fun special_fold_const' 
	(node as (A.BinOp {opr, ...})) = 
	if MathRules.is_commutative opr 
	then
		(fn node as (A.BinOp {attr,opr,lhs,rhs}) => 
			let 
				val node' = commute_node node
				val node'' = special_fold_const node'
			in 
				if equivilent_ast node' node'' then node else node''
			end
		 | node => node
		) (special_fold_const node)
	else special_fold_const node
  | special_fold_const' node = node

(* Detect inverse elements *)
fun inverse_element (node as (A.BinOp {opr=A.Div,lhs,rhs,...})) = (* x/x == 1 *)
	if equivilent_ast lhs rhs then (A.Int 1) else node
  | inverse_element (node as (A.BinOp {opr=A.Minus,lhs,rhs,...})) = (* x-x == 0 *)
  	if equivilent_ast lhs rhs then (A.Int 0) else node
  | inverse_element (node as (A.BinOp {opr=A.Equal,lhs,rhs,...})) = (* x = x == true *)
  	if equivilent_ast lhs rhs then (A.Bool true) else node
  | inverse_element (node as (A.BinOp {opr=A.NEqual,lhs,rhs,...})) = (* x <> x == false *)
  	if equivilent_ast lhs rhs then (A.Bool false) else node
  | inverse_element (node as (A.BinOp {opr=A.BAnd,lhs,rhs,...})) = (* x andAlso x == x *)
  	if equivilent_ast lhs rhs then lhs else node
  | inverse_element (node as (A.BinOp {opr=A.BOr,lhs,rhs,...})) = (* x OrElse x == x *)
  	if equivilent_ast lhs rhs then lhs else node
  | inverse_element x = x


(* Constant Folding *)
fun fold_const (A.BinOp {opr=A.Plus,  lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs+rhs)
  | fold_const (A.BinOp {opr=A.Minus, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs-rhs)
  | fold_const (A.BinOp {opr=A.Times, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs*rhs)
  | fold_const (A.BinOp {opr=A.Div,   lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs div rhs)
  | fold_const (A.BinOp {opr=A.StrConcat,lhs=A.String lhs, rhs=A.String rhs,...}) = A.String (lhs^rhs)
  (* this should know about equality types *)
  | fold_const (A.BinOp {opr=A.Equal, lhs=A.Bool lhs, rhs=A.Bool rhs,...}) = A.Bool (lhs=rhs)
  | fold_const (A.BinOp {opr=A.Equal, lhs=A.String lhs, rhs=A.String rhs,...}) = A.Bool (lhs=rhs)
  | fold_const (A.BinOp {opr=A.Equal, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Bool (lhs=rhs)
  | fold_const (A.BinOp {opr=A.NEqual, lhs=A.Bool lhs, rhs=A.Bool rhs,...}) = A.Bool (lhs<>rhs)
  | fold_const (A.BinOp {opr=A.NEqual, lhs=A.String lhs, rhs=A.String rhs,...}) = A.Bool (lhs<>rhs)
  | fold_const (A.BinOp {opr=A.NEqual, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Bool (lhs<>rhs)
  | fold_const node = node

(* Reorder tree *)
fun comm_reorder_tree (node as (A.BinOp {attr, opr, lhs, rhs})) = 
	if MathRules.is_commutative opr andalso (AstCompare.compare_node lhs rhs) = GREATER then commute_node node else node
  | comm_reorder_tree node = node

(* flatten  a opr b opr c => foldany (op opr) [a,b,c] *)
fun flatten_associativity (node as (A.BinOp {attr, opr=opra, lhs, rhs=(A.BinOp {attr=rattr, opr=oprb, lhs=rlhs, rhs=rrhs})}))
	= if opra = oprb andalso MathRules.is_associative opra then
		A.App {attr=[], exps=[
			A.Var {attr=[], name=(Symbol.fromString "foldany"), symtab=ref (Symtab.symtab Symtab.top_level)},
			A.Op {symbol=AstOps.opr_to_symbol opra,symtab=Symtab.top_level,attr=[]},
			A.List {attr=[], exps=[lhs,rlhs,rrhs]}]}
	else
		node
  | flatten_associativity (node as (A.BinOp {attr, opr=opra, lhs=(A.BinOp {attr=lattr, opr=oprb, lhs=llhs, rhs=lrhs}), rhs}))
	= if opra = oprb andalso MathRules.is_associative opra then
		A.App {attr=[], exps=[
			A.Var {attr=[], name=(Symbol.fromString "foldany"), symtab=ref (Symtab.symtab Symtab.top_level)},
			A.Op {symbol=AstOps.opr_to_symbol opra,symtab=Symtab.top_level,attr=[]},
			A.List {attr=[], exps=[llhs,llhs,rhs]}]}
	else
		node
  | flatten_associativity (node as (A.BinOp {attr, opr=opra, lhs=(A.App {exps=[
		foldany as (A.Var {name,...}), 
		oprb as (A.Op {symbol=sym, ...}), 
		A.List {exps, attr=attr3,...}],attr=attr2}), rhs=rhs}))
	= if (AstOps.opr_to_symbol opra) = sym andalso MathRules.is_associative opra then
		A.App {attr=[], exps=[
			A.Var {attr=[], name=(Symbol.fromString "foldany"), symtab=ref (Symtab.symtab Symtab.top_level)},
			oprb,
			A.List {attr=attr3, exps=(rhs::exps)}]}
	else
		node
  | flatten_associativity node = node

(* sort foldany lists *)
fun sort_foldany_lists (node as (A.App {exps=[
		foldany as (A.Var {name,...}), 
		f, 
		A.List {exps, attr,...}],attr=attr2})) =
	if name=(Symbol.fromString "foldany") then
		(A.App {exps=[
			foldany, 
			f, 
			A.List {exps=(ListMergeSort.sort (fn (a,b) => (AstCompare.compare_node a b) = GREATER) exps),attr=attr}],attr=attr2})
	else
		node
  | sort_foldany_lists node = node

(* Helper debug function *)
fun debugDump name f x = 
	let 
		val x' = f x
	in
		if equivilent_ast x x' then 
			x'
		else
		let
			val _ = print (name ^ ": " ^ (PrettyPrint.ppexp x) ^ " => " ^ (PrettyPrint.ppexp x')^"\n")
		in 
			x'
		end
	end

(* optimisations to apply *)
fun expfun node = (
	  (debugDump "id_func" id_func)
	o (debugDump "special_fold_const" special_fold_const')
	o (debugDump "inverse element" inverse_element)
	o (debugDump "fold_const1" fold_const)
	o (debugDump "sort_foldany_lists" sort_foldany_lists )
	o (debugDump "flatten_associativity" flatten_associativity )
	o (debugDump "fold_const2" fold_const)
	o (debugDump "comm_reorder_tree" comm_reorder_tree)
	) node

fun optConstFold symtab = (AstOps.ast_map_symtab {
	decfun = id,
	expfun = expfun,
	patfun = id,
	bindfun = id,
	tyfun = id,
	oprfun = id,
	clausesfun = id,
	clausefun = id
} symtab; ())

end
