structure AstCompare =
struct

structure A = Ast

(* return true if the nodes should be swapped 
 * we want   App < Var < Int < BinOp
 *
 * This is wrong, we want Int < Var < App < BinOp assuming the tree recurses to the right, so int's are as close to the top as possible
*)

fun compare_opr l r = String.compare (PrettyPrint.ppopr l,PrettyPrint.ppopr r)

fun comparing GREATER rest = GREATER
  | comparing EQUAL rest = rest
  | comparing LESS rest = LESS

fun compare_bool false true = LESS
  | compare_bool false false = EQUAL
  | compare_bool true true = EQUAL
  | compare_bool true false = GREATER

fun compare_list comparitor [] [] = EQUAL
  | compare_list comparitor [] (rh::rt) = LESS
  | compare_list comparitor (lh::lt) [] = GREATER
  | compare_list comparitor (lh::lt) (rh::rt) = 
  	(comparing (comparitor lh rh))
	 (compare_list comparitor lt rt)

fun compare_node (A.BinOp {opr=lopr,lhs=llhs,rhs=lrhs,...}) (A.BinOp {opr=ropr,lhs=rlhs,rhs=rrhs,...}) =
	comparing (compare_opr lopr ropr)
	(comparing (compare_node llhs rlhs)
	(compare_node rlhs rrhs))
  | compare_node (A.BinOp _) _ = GREATER
  | compare_node _ (A.BinOp _) = LESS
 (*  ints *)
  | compare_node (A.Int l) (A.Int r) = Int.compare (l,r)
  | compare_node (A.Int _) _ = GREATER
  | compare_node _ (A.Int _) = LESS
 (* Bools *)
  | compare_node (A.Bool l) (A.Bool r) = compare_bool l r
  | compare_node (A.Bool _) _ = GREATER
  | compare_node _ (A.Bool _) = LESS
 (* Lists *)
  | compare_node (A.List {exps=li,...}) (A.List {exps=ri,...}) = compare_list compare_node li ri
  | compare_node (A.List _) _ = GREATER
  | compare_node _ (A.List _) = LESS
 (* variables *)
  | compare_node (A.Var l) (A.Var r) = Int.compare (Symbol.hash (#name l),Symbol.hash (#name r))
  | compare_node (A.Var _) _ = GREATER
  | compare_node _ (A.Var _) = LESS
 (* Op *)
  | compare_node (A.Op l) (A.Op r) = Int.compare (Symbol.hash (#symbol l),Symbol.hash (#symbol r))
  | compare_node (A.Op _) _ = GREATER
  | compare_node _ (A.Op _) = LESS
 (* Application -- TODO: Make sure we compare the function we're applying not just it's arguments*)
  | compare_node (A.App {exps=lexps,...}) (A.App {exps=rexps,...}) = 
  	(getOpt 
		((List.find (fn x => x <> EQUAL) 
			(map (fn (a,b) => compare_node a b)
				(ListPair.zip(lexps,rexps)))),
		EQUAL))
 (* Failure *)
  | compare_node lhs rhs = raise Fail ("Unknown comparison: " ^ (PrettyPrint.ppexp lhs) ^ " > " ^ (PrettyPrint.ppexp rhs))

end
