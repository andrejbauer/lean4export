inductive Sexp : Type
| atom : String → Sexp
| string : String → Sexp
| integer : Int → Sexp
| double : Float → Sexp
| cons : List Sexp → Sexp

partial def Sexp.toString : Sexp → String
  | .atom s => s
  | .string s => ToString.toString s
  | .integer k => ToString.toString k
  | .double x => ToString.toString x
  | .cons lst => "(" ++ (" ".intercalate $ lst.map toString) ++ ")"

instance: ToString Sexp where
  toString := Sexp.toString

def Sexp.constr (head : String) (lst : List Sexp) : Sexp :=
  .cons ((.atom (":" ++ head)) :: lst)

class Sexpable (α : Type) : Type where
  toSexp : α → Sexp

instance: Sexpable String where
  toSexp := .string

instance: Sexpable Int where
  toSexp := .integer

instance: Sexpable Float where
  toSexp := .double

