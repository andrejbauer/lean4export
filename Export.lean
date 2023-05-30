import Lean
import Sexp

open Lean

structure Context where
  env : Environment

structure State where
  visitedNames : HashMap Name Nat := .insert {} .anonymous 0
  visitedLevels : HashMap Level Nat := .insert {} .zero 0
  visitedExprs : HashMap Expr Nat := {}
  visitedConstants : NameHashSet := {}
  visitedQuot : Bool := false

abbrev M := ReaderT Context <| StateT State IO

def M.run {α : Type} (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

@[inline]
def getIdx {α : Type} [Hashable α] [BEq α] (x : α) (getM : State → HashMap α Nat) (setM : State → HashMap α Nat → State) (rec : M String) : M Nat := do
  let m ← getM <$> get
  if let some idx := m.find? x then
    return idx
  let s ← rec
  let m ← getM <$> get
  let idx := m.size
  IO.println s!"{idx} {s}"
  modify fun st => setM st ((getM st).insert x idx)
  return idx

def dumpName (n : Name) : M Nat := getIdx n (·.visitedNames) ({ · with visitedNames := · }) do
  match n with
  | .anonymous => unreachable!
  | .str n s => return s!"#NS {← dumpName n} {s}"
  | .num n i => return s!"#NI {← dumpName n} {i}"

def dumpLevel (l : Level) : M Nat := getIdx l (·.visitedLevels) ({ · with visitedLevels := · }) do
  match l with
  | .zero | .mvar _ => unreachable!
  | .succ l => return s!"#US {← dumpLevel l}"
  | .max l1 l2 => return s!"#UM {← dumpLevel l1} {← dumpLevel l2}"
  | .imax l1 l2 => return s!"#UIM {← dumpLevel l1} {← dumpLevel l2}"
  | .param n => return s!"#UP {← dumpName n}"

def seq {α : Type} [ToString α] (xs : List α) : String :=
  xs.map toString |> String.intercalate " "

def dumpInfo : BinderInfo → String
  | .default => "#BD"
  | .implicit => "#BI"
  | .strictImplicit => "#BS"
  | .instImplicit => "#BC"

def uint8ToHex (c : UInt8) : String :=
  let d2 := c / 16
  let d1 := c % 16
  (hexDigitRepr d2.toNat ++ hexDigitRepr d1.toNat).toUpper

partial def dumpExpr (e : Expr) : M Nat := do
  if let .mdata _ e := e then
    return (← dumpExpr e)
  getIdx e (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    | .bvar i => return s!"#EV {i}"
    | .sort l => return s!"#ES {← dumpLevel l}"
    | .const n us =>
      return s!"#EC {← dumpName n} {← seq <$> us.mapM dumpLevel}"
    | .app f e => return s!"#EA {← dumpExpr f} {← dumpExpr e}"
    | .lam n d b bi => return s!"#EL {dumpInfo bi} {← dumpName n} {← dumpExpr d} {← dumpExpr b}"
    | .letE n d v b _ => return s!"#EZ {← dumpName n} {← dumpExpr d} {← dumpExpr v} {← dumpExpr b}"
    | .forallE n d b bi => return s!"#EP {dumpInfo bi} {← dumpName n} {← dumpExpr d} {← dumpExpr b}"
    | .mdata .. | .fvar .. | .mvar .. => unreachable!
    -- extensions compared to Lean 3
    | .proj s i e => return s!"#EJ {← dumpName s} {i} {← dumpExpr e}"
    | .lit (.natVal i) => return s!"#ELN {i}"
    | .lit (.strVal s) => return s!"#ELS {s.toUTF8.toList.map uint8ToHex |> seq}"


def Sexp.fromName (n : Name) : Sexp :=
  match n with
  | .anonymous => .constr "anonymous" []
  | .str mdl nm =>
    .constr "name" $ (.integer mdl.hash) :: (.integer nm.hash) :: (toAtoms n).reverse
  | .num mdl k =>
    .constr "name" $ (.integer mdl.hash) :: (.integer (hash k)) :: (toAtoms n).reverse
  where
    toAtoms (n : Name) : List Sexp :=
      match n with
      | .anonymous => [.atom "_"]
      | .str mdl s => .atom s :: toAtoms mdl
      | .num mdl k => .atom s!"num{k}" :: toAtoms mdl

instance: Sexpable Name where
  toSexp := Sexp.fromName

def Sexp.fromLevel : Level → Sexp
  | .zero => .constr "lzero" []
  | .succ lvl =>  .constr "lsucc" [fromLevel lvl]
  | .max lvl1 lvl2 => .constr "max" [fromLevel lvl1, fromLevel lvl2]
  | .imax lvl1 lvl2 => .constr "imax" [fromLevel lvl1, fromLevel lvl2]
  | .param nm => toSexp nm
  | .mvar mv => toSexp mv.name


instance: Sexpable Level where
  toSexp := Sexp.fromLevel

def Sexp.fromExpr : Expr → Sexp
  | .bvar k => constr "var" [toSexp k]
  | .fvar fv => toSexp fv.name
  | .mvar mvarId => constr "meta" [toSexp mvarId.hash]
  | .sort (u : Level) => constr "level" [toSexp u]
  | .const (declName : Name) (us : List Level) =>
    sorry
  | .app (fn : Expr) (arg : Expr) =>
    sorry
  | .lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) =>
    sorry
  | .forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) =>
    sorry
  | .letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool) =>
    sorry
  | .lit : Literal → Expr =>
    sorry
  | .mdata (data : MData) (expr : Expr) =>
    sorry
  | .proj (typeName : Name) (idx : Nat) (struct : Expr) =>
    sorry

instance: Sexpable Expr where
  toSexp := Sexp.fromExpr

instance: Sexpable ConstantVal where
  toSexp := Sexp.fromConstantVal

instance: Sexpable QuotKind where
  toSexp := fun k =>
    match k with
  | .type => Sexp.constr "type" []
  | .ctor => Sexp.constr "ctor" []
  | .lift => Sexp.constr "lift" []
  | .ind  => Sexp.constr "ind" []

def Sexp.fromConstantInfo : ConstantInfo → Sexp
  | .axiomInfo _ => constr "axiom" []
  | .defnInfo val => toSexp val.value
  | .thmInfo val => toSexp val.value
  | .opaqueInfo val => toSexp val.value
  | .quotInfo val => constr "quot-info" [toSexp val.kind, toSexp val.toConstantVal.name]
  | .inductInfo _ => constr "data-or-record" []
  | .ctorInfo val => constr "constructor" [toSexp val.induct]
  | .recInfo _ => constr "recursor" []

instance: Sexpable ConstantInfo where
  toSexp := Sexp.fromConstantInfo

def Sexp.fromConstant (nm : Name) (c : ConstantInfo) : Sexp :=
  .constr "definition" [toSexp nm, toSexp c.type, Sexp.fromConstantInfo c]

partial def dumpConstant (c : Name) : M Unit := do
  if (← get).visitedConstants.contains c then
    return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match (← read).env.find? c |>.get! with
  | .axiomInfo val => do
    dumpDeps val.type
    IO.println s!"#AX {← dumpName c} {← dumpExpr val.type} {← seq <$> val.levelParams.mapM dumpName}"
  | .defnInfo val => do
    if val.safety != .safe then
      return
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#DEF {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#DEF {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
  | .opaqueInfo _ => return
  | .quotInfo _ =>
    -- Lean 4 uses 4 separate `Quot` declarations in the environment, but Lean 3 uses a single special declarations
    if (← get).visitedQuot then
      return
    modify ({ · with visitedQuot := true })
    -- the only dependency of the quot module
    dumpConstant `Eq
    IO.println s!"#QUOT"
  | .inductInfo val => do
    dumpDeps val.type
    for ctor in val.ctors do
      dumpDeps ((← read).env.find? ctor |>.get!.type)
    let ctors ← (·.join) <$> val.ctors.mapM fun ctor => return [← dumpName ctor, ← dumpExpr ((← read).env.find? ctor |>.get!.type)]
    IO.println s!"#IND {val.numParams} {← dumpName c} {← dumpExpr val.type} {val.numCtors} {seq ctors} {← seq <$> val.levelParams.mapM dumpName}"
  | .ctorInfo _ | .recInfo _ => return
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
