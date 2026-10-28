import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingTheorem

namespace OAI.Algorithms

/-! Actual emitted original-ID head lists inherit the searched packing's
head bound. Taking the maximum is proof-only and introduces no new search. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LeafHeadSetupProgram

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

omit [DecidableEq I] in
theorem source_selected_length_le
    (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) :
    (selectedHeads n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val)).length ≤
    (Packing.headSupport (Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x y) t g).card := by
  classical
  let : NeZero r := ⟨by have := g.isLt; omega⟩
  let rows := LeafHeadFactorsProgram.sourceRows owner factor a tail terms w
  let p := HeadIdentifierProgram.predicate rows (HeadIdentifierProgram.lowBits low)
    (t.val*r+g.val)
  let S := Packing.headSupport (Packing.computedWords owner factor a tail terms
    (LeafHeadFactorsProgram.indices n N) x y) t g
  let f : Fin (HeadIdentifierProgram.count p n) → S := fun i =>
    ⟨HeadIdentifierProgram.headOrder p n i, by
      apply (Packing.mem_headSupport _ _ _ _).mpr
      exact ((selectedHeads_source_mem owner factor a tail terms w x y hy hx low t g
        (HeadIdentifierProgram.headOrder p n i)).mp (List.getElem_mem i.isLt)).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact HeadIdentifierProgram.headOrder_injective p n (congrArg Subtype.val hij)
  change HeadIdentifierProgram.count p n ≤ S.card
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

def maxSelected (n Q r : ℕ) (rows : List (List Bool)) (low : List Bool) : ℕ :=
  (Finset.univ : Finset (Fin Q × Fin r)).sup
    (fun z => (selectedHeads n rows low (z.1.val*r+z.2.val)).length)

theorem selected_le_max (n Q r : ℕ) (rows : List (List Bool)) (low : List Bool)
    (t : Fin Q) (g : Fin r) :
    (selectedHeads n rows low (t.val*r+g.val)).length ≤ maxSelected n Q r rows low :=
  Finset.le_sup (f := fun z : Fin Q × Fin r =>
    (selectedHeads n rows low (z.1.val*r+z.2.val)).length) (Finset.mem_univ (t,g))

theorem maxSelected_rat_le (n Q r : ℕ) (rows : List (List Bool)) (low : List Bool)
    (bound : ℚ) (hb : 0 ≤ bound)
    (h : ∀ (t : Fin Q) (g : Fin r),
      ((selectedHeads n rows low (t.val*r+g.val)).length : ℚ) ≤ bound) :
    (maxSelected n Q r rows low : ℚ) ≤ bound := by
  unfold maxSelected
  rcases (Finset.univ : Finset (Fin Q × Fin r)).eq_empty_or_nonempty with he | hn
  · simpa only [he,Finset.sup_empty,Nat.bot_eq_zero,Nat.cast_zero] using hb
  · obtain ⟨z,_,hz⟩ := Finset.exists_mem_eq_sup _ hn
      (fun z : Fin Q × Fin r => (selectedHeads n rows low (z.1.val*r+z.2.val)).length)
    rw [hz]
    exact h z.1 z.2

omit [DecidableEq I] in
theorem source_max_le_of_energy
    (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x : ℚ) (hr : 0 < r)
    (hy : ((n:ℚ)/(2*(r:ℚ)))^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool)
    (henergy : Packing.headEnergy (Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) ≤
        ((n:ℚ)/(2*(r:ℚ)))^2) :
    (maxSelected n Q r (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(n:ℚ)/(2*(r:ℚ)) := by
  let : NeZero r := ⟨Nat.ne_of_gt hr⟩
  have hrq : (0:ℚ) < r := by exact_mod_cast hr
  apply maxSelected_rat_le _ _ _ _ _ _ (by positivity)
  intro t g
  have hlen := source_selected_length_le owner factor a tail terms w x
    ((n:ℚ)/(2*(r:ℚ))) hy hx low t g
  have hhead := Packing.head_count_upper (y := (n:ℚ)/(2*(r:ℚ)))
    (Packing.computedWords owner factor a tail terms (LeafHeadFactorsProgram.indices n N)
      x ((n:ℚ)/(2*(r:ℚ)))) (by positivity) henergy t g
  change ((Packing.headSupport _ t g).card : ℚ) ≤ _ at hhead
  have hlenQ : ((selectedHeads n
      (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val)).length : ℚ) ≤
      ((Packing.headSupport (Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) t g).card : ℚ) := by
    exact_mod_cast hlen
  calc
    _ ≤ ((Packing.headSupport (Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) t g).card : ℚ) := hlenQ
    _ ≤ (n:ℚ)/r+(n:ℚ)/(2*(r:ℚ)) := by simpa only [Fintype.card_fin] using hhead
    _ = _ := by field_simp; ring

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
