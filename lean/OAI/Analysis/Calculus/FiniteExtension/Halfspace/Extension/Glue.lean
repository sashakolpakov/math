import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Glue

/-! Classical gluing from genuinely one-sided Taylor jets.  Neither side
is assumed smooth outside its own closed halfspace. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

open OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_of_closed_halves (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f : E → F)
    (hp : ContinuousOn f {x | 0 ≤ ℓ x}) (hm : ContinuousOn f {x | ℓ x ≤ 0}) :
    Continuous f := by
  have hu : {x | 0 ≤ ℓ x} ∪ {x | ℓ x ≤ 0} = univ := by
    ext x
    simp only [mem_union, Set.mem_ofPred_eq, mem_univ, iff_true]
    exact le_total _ _
  have h := (continuousOn_union_iff_of_isClosed
    (isClosed_le continuous_const hℓ) (isClosed_le hℓ continuous_const)).mpr ⟨hp, hm⟩
  simpa only [hu, continuousOn_univ] using h

theorem hasFDerivAt_of_closed_halves (ℓ : E → ℝ) (hℓ : Continuous ℓ)
    (f : E → F) (D : E → E →L[ℝ] F)
    (hp : ∀ x, 0 ≤ ℓ x → HasFDerivWithinAt f (D x) {y | 0 ≤ ℓ y} x)
    (hm : ∀ x, ℓ x ≤ 0 → HasFDerivWithinAt f (D x) {y | ℓ y ≤ 0} x)
    (x : E) : HasFDerivAt f (D x) x := by
  have hpos : HasFDerivWithinAt f (D x) {y | 0 ≤ ℓ y} x := by
    by_cases hx : 0 ≤ ℓ x
    · exact hp x hx
    · apply HasFDerivWithinAt.of_notMem_closure
      simpa only [(isClosed_le continuous_const hℓ).closure_eq, Set.mem_ofPred_eq] using hx
  have hneg : HasFDerivWithinAt f (D x) {y | ℓ y ≤ 0} x := by
    by_cases hx : ℓ x ≤ 0
    · exact hm x hx
    · apply HasFDerivWithinAt.of_notMem_closure
      simpa only [(isClosed_le hℓ continuous_const).closure_eq, Set.mem_ofPred_eq] using hx
  have hu : {y | 0 ≤ ℓ y} ∪ {y | ℓ y ≤ 0} = univ := by
    ext y
    simp only [mem_union, Set.mem_ofPred_eq, mem_univ, iff_true]
    exact le_total _ _
  simpa only [hu, hasFDerivWithinAt_univ] using hpos.union hneg

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_levelGlue_of_closed_halves (ℓ : E → ℝ) (hℓ : Continuous ℓ)
    (f g : E → F) (hf : ContinuousOn f {x | 0 ≤ ℓ x})
    (hg : ContinuousOn g {x | ℓ x ≤ 0})
    (heq : ∀ x, ℓ x = 0 → f x = g x) : Continuous (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g) := by
  apply continuous_of_closed_halves ℓ hℓ
  · apply hf.congr
    intro x hx
    exact ite_eq_left hx
  · apply hg.congr
    intro x hx
    by_cases hp : 0 ≤ ℓ x
    · exact (ite_eq_left hp).trans (heq x (le_antisymm hx hp))
    · exact ite_eq_right hp

/-- Matching finite Taylor jets on complementary closed sides give an
actual global classical Taylor expansion, including on the interface. -/
theorem hasFTaylorSeriesUpTo_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ)
    {N : ℕ} (f g : E → F) (p q : E → FormalMultilinearSeries ℝ E F)
    (hp : HasFTaylorSeriesUpToOn N f p {x | 0 ≤ ℓ x})
    (hq : HasFTaylorSeriesUpToOn N g q {x | ℓ x ≤ 0})
    (heq : ∀ m ≤ N, ∀ x, ℓ x = 0 → p x m = q x m) :
    HasFTaylorSeriesUpTo N (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g)
      (fun x m => OAI.Analysis.PDE.Schauder.levelGlue ℓ (fun y => p y m) (fun y => q y m) x) := by
  constructor
  · intro x
    by_cases hx : 0 ≤ ℓ x
    · simpa only [OAI.Analysis.PDE.Schauder.levelGlue, ite_eq_left hx] using hp.zero_eq x hx
    · simpa only [OAI.Analysis.PDE.Schauder.levelGlue, ite_eq_right hx] using hq.zero_eq x (le_of_not_ge hx)
  · intro m hm
    have hmN : m < N := by exact_mod_cast hm
    apply hasFDerivAt_of_closed_halves ℓ hℓ
    · intro x hx
      simp only [OAI.Analysis.PDE.Schauder.levelGlue, ite_eq_left hx]
      apply (hp.fderivWithin m hm x hx).congr'
      · intro y hy
        exact ite_eq_left hy
      · exact hx
    · intro x hx
      have hd : OAI.Analysis.PDE.Schauder.levelGlue ℓ (fun y => p y m.succ) (fun y => q y m.succ) x = q x m.succ := by
        by_cases hp0 : 0 ≤ ℓ x
        · exact (ite_eq_left hp0).trans (heq _ (by omega) x (le_antisymm hx hp0))
        · exact ite_eq_right hp0
      rw [hd]
      apply (hq.fderivWithin m hm x hx).congr'
      · intro y hy
        by_cases hp0 : 0 ≤ ℓ y
        · exact (ite_eq_left hp0).trans (heq m (by omega) y (le_antisymm hy hp0))
        · exact ite_eq_right hp0
      · exact hx
  · intro m hm
    apply continuous_levelGlue_of_closed_halves ℓ hℓ _ _ (hp.cont m hm) (hq.cont m hm)
    exact heq m (by exact_mod_cast hm)

end OAI.Analysis.Calculus.FiniteExtension
