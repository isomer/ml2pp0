structure MathRules =
struct

structure A = Ast

(* a opr b == b opr a *)
fun is_commutative A.Plus = true
  | is_commutative A.Times = true
  | is_commutative A.Equal = true
  | is_commutative A.NEqual = true
  | is_commutative A.BAnd = true
  | is_commutative A.BOr = true
  | is_commutative _ = false (* by default things are not commutative *)

(* (a opr b) opr c == a opr (b opr c) *)
fun is_associative A.Plus = true
  | is_associative A.Times = true
  | is_associative A.Concat = true
  | is_associative A.StrConcat = true
  | is_associative A.BAnd = true
  | is_associative A.BOr = true
  | is_associative _ = false (* by default *)

(* is the rhs an identity *)
fun is_id_func_rhs A.Div _ (A.Int 1) 	= true
  | is_id_func_rhs A.StrConcat _ (A.String "") = true
(*  | is_id_func_rhs A.Concat _ (A.List {exps=[],...})  = true *)
  | is_id_func_rhs A.BAnd _ (A.Bool true) = true
  | is_id_func_rhs A.BOr _ (A.Bool false) = true
  | is_id_func_rhs _ _ _ 		= false

(* is the lhs an identity *)
fun is_id_func_lhs A.Plus (A.Int 0) _ 	= true
  | is_id_func_lhs A.Minus (A.Int 0) _ 	= true
  | is_id_func_lhs A.Times (A.Int 1) _ 	= true
  | is_id_func_lhs A.StrConcat (A.String "") _ = true
(*  | is_id_func_lhs A.Concat (A.List {exps=[],...}) _  = true *)
(*  | is_id_func_lhs A.Equal (A.Var {name=sym,...}) _ = (Symbol.toString sym) = "true" *)
  | is_id_func_lhs A.Equal (A.Bool n) _ = n
  | is_id_func_lhs A.NEqual (A.Bool n) _ = not n
  | is_id_func_lhs _ _ _ 		= false

(* Is this constant *)
fun is_constant (A.Int _) = true
  | is_constant (A.String _) = true
(*  | is_constant (A.List _) = true *)
  | is_constant (A.Bool _) = true
  | is_constant _ = false

(* f(f(x)) = f(x) *)
fun is_idempotent A.BAnd = true
  | is_idempotent A.BOr = true
  | is_idempotent A.Mod = true
  | is_idempotent _ = false

(* f(f(x)) = x *)
fun (*is_involution A.UMinus = true   
  | is_involution A.BNot = true 
  | *)is_involution _ = false

end
