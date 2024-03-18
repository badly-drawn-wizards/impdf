import Std
import Init

open Std

class Store (α : outParam Type) (β : outParam Type) (S : Type) where
  empty : S
  get : α → S → β
  put : α → β → S → S

instance hashmapStore [Hashable α] [BEq α] [Inhabited β] : Store α β (HashMap α β) where
  empty := HashMap.empty
  get a σ := σ.findD a default
  put α β σ := σ.insert α β

abbrev Var := Int
abbrev St := Store Var Int

inductive Ty where
  | int
  | bool

@[reducible] def Ty.type : Ty → Type
  | .int => Int
  | .bool => Bool

inductive Expr : Ty → Type where
  | litInt : Int → Expr .int
  | litBool : Bool → Expr .bool
  | varInt : Var → Expr .int
  | add : Expr .int → Expr .int → Expr .int
  | minus : Expr .int → Expr .int
  | lt : Expr .int → Expr .int → Expr .bool
  | eq : Expr .int → Expr .int → Expr .bool

inductive Prog
  | skip : Prog
  | seq : Prog → Prog → Prog
  | while : Expr .bool → Prog → Prog
--  | ift : Expr .bool → Prog → Prog → Prog
  | assign : Var → Expr .int → Prog
#eval Lean.versionString

inductive ProgLoc : Prog → Type where
  | seqLeft : ProgLoc p₁ → ProgLoc (.seq p₁ p₂)
  | seqRight : ProgLoc p₂ → ProgLoc (.seq p₁ p₂)
  | while : ProgLoc p → ProgLoc (.while e p)
  | here : ProgLoc p
deriving BEq, Ord

def eval [St S] (σ : S) (v : Expr ty) : ty.type := 
  match v with
    | .add e₁ e₂ => (eval σ e₁) + (eval σ e₁)
    | .minus e => -(eval σ e)
    | .litInt i => i
    | .varInt v => Store.get v σ
    | .eq e₁ e₂ => (eval σ e₁) = (eval σ e₁)
    | .lt e₁ e₂ => (eval σ e₁) < (eval σ e₁)
    | .litBool b => b


inductive Step [St S] : Prog × S → Prog × S → Prop where
  | skip : Step (.seq .skip p, σ) (p, σ)
  | seq : Step (p₁, σ₁) (p₁', σ₂) → Step (.seq p₁ p₂, σ₁) (.seq p₁' p₂, σ₂)
  | whilett : eval σ e = true → Step (.while e p, σ) (.seq p (.while e p), σ)
  | whileff : eval σ e = false → Step (.while e p, σ) (.skip, σ)
  | assign : Step (.assign v e, σ) (.skip, Store.put v (eval σ e) σ)

inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : Star R a a
  | trans : R a b → Star R b c → Star R a c

class Join (α : Type) where
  bot : α
  join : α → α → α

instance [Join α] : LE α where
  le a b := Join.join a b = b

class JoinLe (α : Type) [BEq α] extends Join α where
  joinLE (a b : α): α × Bool := 
    let u := join a b
    (u, u == b)

instance : JoinLe Unit where
  bot := ()
  join _ _ := ()

/- protected def HashMap.toOrderedArray [Hashable α] [BEq α] [Ord α] (h : HashMap α β) : Array (α × β) := -/
/-   h.toArray.insertionSort (fun (a,_) (b,_) => compare a b == Ordering.lt) -/
/- instance [Hashable α] [Ord α] [BEq α] [BEq β] : BEq (HashMap α β) where -/
/-   beq a b := HashMap.toOrderedArray a == HashMap.toOrderedArray b -/
/- instance [Hashable α] [BEq α] [BEq β] [JoinLe β] : Join (HashMap α β) where -/
/-   bot := HashMap.empty -/
/-   join := HashMap.mergeWith (fun _ => Join.join) -/
  /- joinLE := flip StateT.run false <| HashMap.mergeWithM <| fun _ a b => do -/
  /-   let (u, b) := JoinLe.joinLE a b -/


protected def Std.RBSet.pop? (s : RBSet α cmp) : Option (α × RBSet α cmp) := 
  s.findP? (λ _ => .eq) 
  |>.map λ e => (e, s.erase (fun _ => .eq))

/- protected def Std.RBMap.insertWith (s : RBMap α β cmp) (f : α → β → β → β) (a : α) (b : β) := -/
/-   s.mergeWith f (RBMap.single a b) -/

namespace WorkList

variable (node fact : Type) [Ord node] [BEq fact] [JoinLe fact]
structure State where
  facts : RBMap node fact compare
  work : RBSet node compare

structure Spec where
  affects : RBMap node (RBSet node compare) compare
  transfer : (node → fact) → (node → fact)

end WorkList

namespace WorkList
variable {node fact : Type} [Ord node] [BEq fact] [JoinLe fact]

def State.nodeFact (w : State node fact) : node → fact := flip w.facts.findD Join.bot

def Spec.step (spec : Spec node fact) (st : State node fact) : State node fact × Bool :=
    match st.work.pop? with
    | .some (node, work') =>
      let fact := st.nodeFact node
      let tfr := spec.transfer st.nodeFact node
      let (fact', unchanged) := JoinLe.joinLE tfr fact
      let st' := { 
        facts := if unchanged then st.facts else st.facts.insert node fact'
        work := work'.union <| spec.affects.findD node RBSet.empty
      }
      (st', !unchanged)
    | .none => (st, false)

end WorkList
