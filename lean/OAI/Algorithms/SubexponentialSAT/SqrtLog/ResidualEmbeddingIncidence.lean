import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingBranch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsPerturbation

namespace OAI.Algorithms

/-! Residual incidence rows may be stored at original ambient indices by
padding high coordinates with zero. Their jet and evaluation are unchanged. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V A R : Type*} [Fintype V] [DecidableEq V]

def padZero [Zero A] (H : Finset V) (f : Free H → A) (v : V) : A :=
  if hv : v ∉ H then f ⟨v, hv⟩ else 0

omit [Fintype V] in
@[simp] theorem padZero_low [Zero A] (H : Finset V) (f : Free H → A) (v : Free H) :
    padZero H f v.val = f v := by simp [padZero, v.property]

omit [Fintype V] in
@[simp] theorem padZero_high [Zero A] (H : Finset V) (f : Free H → A) (v : V)
    (hv : v ∈ H) : padZero H f v = 0 := by simp [padZero, hv]

theorem sum_padZero [AddCommMonoid A] (H : Finset V) (f : Free H → A) :
    (∑ v, padZero H f v) = ∑ v, f v := by
  calc
    _ = ∑ v ∈ (Finset.univ : Finset (Free H)).map (inclusion H), padZero H f v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v hv hn
      have hH : v ∈ H := by
        by_contra h
        exact hn (Finset.mem_map.mpr ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩)
      exact padZero_high H f v hH
    _ = _ := by
      rw [Finset.sum_map]
      simp only [inclusion_apply, padZero_low]

variable [CommRing R]

/-- This version is polymorphic in both variable universes. -/
theorem map_variableZ {U W : Type*} [DecidableEq U] [DecidableEq W]
    (e : U ↪ W) (v : U) (p : Polynomial R) :
    (Moments.variableZ v p).map (poly e) = Moments.variableZ (e v) p := by
  ext j
  simp [Moments.variableZ_coeff]

theorem incidenceZ_pad (H : Finset V) (row : Free H → Polynomial R) (theta beta : R) :
    (Moments.incidenceZ row theta beta).map (poly (inclusion H)) =
      Moments.incidenceZ (padZero H row) theta beta := by
  have hscalar : poly (inclusion H) (Squarefree.scalar beta) = Squarefree.scalar beta := by
    change poly (inclusion H) (monomial ∅ beta) = monomial ∅ beta
    simp
  simp only [Moments.incidenceZ, Polynomial.map_add, Polynomial.map_C,
    hscalar, Polynomial.map_sum, map_variableZ]
  congr 1
  symm
  have h : (fun v => Moments.variableZ v (Moments.rowDelta (padZero H row v) theta)) =
      padZero H (fun v => Moments.variableZ v.val (Moments.rowDelta (row v) theta)) := by
    funext v
    by_cases hv : v ∉ H
    · simp [padZero, hv]
    · simp [padZero, hv, Moments.rowDelta, Moments.variableZ]
  rw [h, sum_padZero]
  simp only [inclusion_apply]

theorem incidenceJet_pad (H : Finset V) (row : Free H → Polynomial R) (theta beta : R) :
    jet (inclusion H) (Moments.incidenceJet row theta beta) =
      Moments.incidenceJet (padZero H row) theta beta := by
  simp [jet, Moments.incidenceJet, incidenceZ_pad]

omit [Fintype V] in
theorem eval_jet_branch (H : Finset V) (a : H → Bool) (b : Free H → Bool)
    (f : Jet (Free H) R) :
    Moments.jetEval (boolValue (HighIncidence.glue H a b))
      (boolValue_idempotent (HighIncidence.glue H a b)) (jet (inclusion H) f) =
    Moments.jetEval (boolValue b) (boolValue_idempotent b) f := by
  rw [eval_jet]
  have h : (fun v : Free H => boolValue (R := R) (HighIncidence.glue H a b)
      (inclusion H v)) = boolValue b := by
    funext v
    simp [boolValue, HighIncidence.glue, v.property]
  simp only [h]

theorem sum_eval_jet_branch (H : Finset V) (a : H → Bool) (f : (Free H → Bool) → Jet (Free H) R) :
    (∑ b : Free H → Bool,
      Moments.jetEval (boolValue (HighIncidence.glue H a b))
        (boolValue_idempotent (HighIncidence.glue H a b)) (jet (inclusion H) (f b))) =
    ∑ b : Free H → Bool, Moments.jetEval (boolValue b) (boolValue_idempotent b) (f b) := by
  apply Finset.sum_congr rfl
  intro b hb
  exact eval_jet_branch H a b (f b)

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
