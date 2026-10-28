import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblySemantics

namespace OAI.Algorithms

/-!
# Local semantic refinement of generated moment sources

Raw literals may use a different term order and different zero padding from
the reference builder. Equality of the local outside weights, inner weights,
and factor values suffices. No equality of serialized source programs or of
their final jets is an input to the refinement theorem.
-/

namespace SubexponentialSAT.SubexpSourceSemantics

open SubexpAlgorithm

private theorem sum_map_eq {A B R : Type*} [AddMonoid R]
    {xs : List A} {ys : List B} {rel : A → B → Prop}
    (h : List.Forall₂ rel xs ys) (f : A → R) (g : B → R)
    (he : ∀ a b, rel a b → f a = g b) : (xs.map f).sum = (ys.map g).sum := by
  induction h with
  | nil => rfl
  | @cons a b xs ys hab hrest ih =>
      simp only [List.map_cons, List.sum_cons, he a b hab, ih]

private theorem prod_map_eq {A B R : Type*} [Monoid R]
    {xs : List A} {ys : List B} {rel : A → B → Prop}
    (h : List.Forall₂ rel xs ys) (f : A → R) (g : B → R)
    (he : ∀ a b, rel a b → f a = g b) : (xs.map f).prod = (ys.map g).prod := by
  induction h with
  | nil => rfl
  | @cons a b xs ys hab hrest ih =>
      simp only [List.map_cons, List.prod_cons, he a b hab, ih]

section Local

variable {A B R : Type*} [Semiring R]

def TermRel (left : A → R) (right : B → R)
    (a : Algorithm.WeightedTerm A) (b : Algorithm.WeightedTerm B) : Prop :=
  left a.weight = right b.weight ∧
    (a.group.map left).eval = (b.group.map right).eval

def BlockRel (left : A → R) (right : B → R)
    (a : Block A) (b : Block B) : Prop :=
  left a.outside = right b.outside ∧
    List.Forall₂ (List.Forall₂ (TermRel left right)) a.groups b.groups

theorem product_value_eq {left : A → R} {right : B → R}
    [One A] [One B] (hl : left 1 = 1) (hr : right 1 = 1)
    {as : List (Algorithm.Expr A)} {bs : List (Algorithm.Expr B)}
    (h : List.Forall₂ (fun a b => (a.map left).eval = (b.map right).eval) as bs) :
    ((Algorithm.Expr.product as).map left).eval =
      ((Algorithm.Expr.product bs).map right).eval := by
  induction h with
  | nil => simpa only [Algorithm.Expr.product, Algorithm.Expr.map, Algorithm.Expr.eval] using hl.trans hr.symm
  | @cons a b as bs hab hrest ih =>
      simp only [Algorithm.Expr.product, Algorithm.Expr.map, Algorithm.Expr.eval, hab, ih]

private theorem group_value_eq {left : A → R} {right : B → R}
    {as : List (Algorithm.WeightedTerm A)} {bs : List (Algorithm.WeightedTerm B)}
    (h : List.Forall₂ (TermRel left right) as bs) :
    (as.map fun t => left t.weight * (t.group.map left).eval).sum =
      (bs.map fun t => right t.weight * (t.group.map right).eval).sum := by
  apply sum_map_eq h
  intro a b hab
  rw [hab.1, hab.2]

private theorem block_value_eq {left : A → R} {right : B → R}
    {a : Block A} {b : Block B} (h : BlockRel left right a b) :
    left a.outside * (a.groups.map fun ts =>
      (ts.map fun t => left t.weight * (t.group.map left).eval).sum).prod =
    right b.outside * (b.groups.map fun ts =>
      (ts.map fun t => right t.weight * (t.group.map right).eval).sum).prod := by
  rw [h.1]
  apply congrArg (right b.outside * ·)
  apply prod_map_eq h.2
  intro as bs hab
  exact group_value_eq hab

theorem moment_value_eq [Zero A] [One A] [Zero B] [One B]
    (left : A → R) (right : B → R)
    (hl0 : left 0 = 0) (hl1 : left 1 = 1)
    (hr0 : right 0 = 0) (hr1 : right 1 = 1)
    {as : List (Block A)} {bs : List (Block B)}
    (h : List.Forall₂ (BlockRel left right) as bs) :
    ((momentExpression as).map left).eval =
      ((momentExpression bs).map right).eval := by
  rw [map_momentExpression left hl0 hl1, map_momentExpression right hr0 hr1,
    momentExpression_eval, momentExpression_eval]
  simp only [List.map_map, Block.map, Algorithm.WeightedTerm.map, Function.comp_def]
  exact sum_map_eq h _ _ (fun _ _ hab => block_value_eq hab)

end Local

section Raw

variable {D : ℕ} {C R : Type*} [CommSemiring R]

def decodeRaw (decode : C → R) (raw : SymbolicCost.CoeffList D C) :
    SymbolicCost.CoeffList D R := raw.map fun term => (term.1, decode term.2)

private theorem map_map {L S T : Type*} (f : L → S) (g : S → T)
    (e : Algorithm.Expr L) :
    (e.map f).map g = e.map (fun x => g (f x)) := by
  induction e with
  | lit x => rfl
  | add e f he hf => simp only [Algorithm.Expr.map, he, hf]
  | mul e f he hf => simp only [Algorithm.Expr.map, he, hf]

private theorem jet_congr
    (left right : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (h : ∀ a ∈ Algorithm.exponentList D (2 * D + 1),
      ((left a).map SymbolicCost.denote).eval =
        ((right a).map SymbolicCost.denote).eval) :
    Algorithm.executeRawJet left = Algorithm.executeRawJet right := by
  rw [Algorithm.executeRawJet_eq, Algorithm.executeRawJet_eq]
  apply List.map_congr_left
  intro r hr
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [h a ha]

/-- Refinement from actual locally checked literals and group programs to
the reference r-color jet, without a source-byte identity hypothesis. The
actual zero and one literals may be padded singleton records. -/
theorem jet_eq_of_local [Zero (SymbolicCost.CoeffList D C)]
    [One (SymbolicCost.CoeffList D C)]
    (decode : C → R)
    (actual : (Fin D → ℕ) → List (Block (SymbolicCost.CoeffList D C)))
    (reference : (Fin D → ℕ) → List (Block (SymbolicCost.CoeffList D R)))
    (hzero : SymbolicCost.denote (decodeRaw decode (0 : SymbolicCost.CoeffList D C)) = 0)
    (hone : SymbolicCost.denote (decodeRaw decode (1 : SymbolicCost.CoeffList D C)) = 1)
    (hlocal : ∀ a ∈ Algorithm.exponentList D (2 * D + 1),
      List.Forall₂ (BlockRel (fun raw => SymbolicCost.denote (decodeRaw decode raw))
        SymbolicCost.denote) (actual a) (reference a)) :
    Algorithm.executeRawJet (fun a => (momentExpression (actual a)).map (decodeRaw decode)) =
      SubexpAlgorithm.executeJet reference := by
  unfold SubexpAlgorithm.executeJet
  apply jet_congr
  intro a ha
  let : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  let : One (SymbolicCost.CoeffList D R) := ⟨SubexpAlgorithm.rawOne D⟩
  have h := moment_value_eq (fun raw => SymbolicCost.denote (decodeRaw decode raw))
    SymbolicCost.denote hzero hone (by rfl) (SubexpAlgorithm.rawOne_denote D) (hlocal a ha)
  simpa only [map_map, SubexpAlgorithm.rawMomentExpression] using h

end Raw

end SubexponentialSAT.SubexpSourceSemantics

end OAI.Algorithms
