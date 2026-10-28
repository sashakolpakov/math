import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Compact

/-! Differentiability of actual functions glued along a level set. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def levelGlue (ℓ : E → ℝ) (f g : E → F) (x : E) : F :=
  if 0 ≤ ℓ x then f x else g x

theorem hasFDerivAt_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f g : E → F)
    (x : E) (f' g' : E →L[ℝ] F) (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hval : ∀ y, ℓ y = 0 → f y = g y) (hder : ℓ x = 0 → f' = g') :
    HasFDerivAt (levelGlue ℓ f g) (if 0 ≤ ℓ x then f' else g') x := by
  rcases lt_trichotomy 0 (ℓ x) with hx | hx | hx
  · rw [ite_eq_left hx.le]
    apply hf.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const hℓ).mem_nhds hx] with y hy
    exact ite_eq_left (le_of_lt hy)
  · have hx0 : ℓ x = 0 := hx.symm
    rw [ite_eq_left (by linarith)]
    have hp : HasFDerivWithinAt (levelGlue ℓ f g) f' {y | 0 ≤ ℓ y} x := by
      apply hf.hasFDerivWithinAt.congr'
      · intro y hy
        exact ite_eq_left hy
      · exact hx0.ge
    have hm : HasFDerivWithinAt (levelGlue ℓ f g) f' {y | ℓ y ≤ 0} x := by
      rw [hder hx0]
      apply hg.hasFDerivWithinAt.congr'
      · intro y hy
        by_cases hh : 0 ≤ ℓ y
        · exact (ite_eq_left hh).trans (hval y (le_antisymm hy hh))
        · exact ite_eq_right hh
      · exact hx0.le
    have hu : {y | 0 ≤ ℓ y} ∪ {y | ℓ y ≤ 0} = Set.univ := by
      ext y
      simp only [mem_union, Set.mem_ofPred_eq, mem_univ, iff_true]
      exact le_total 0 (ℓ y)
    simpa only [hu, hasFDerivWithinAt_univ] using hp.union hm
  · rw [ite_eq_right (not_le.mpr hx)]
    apply hg.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hℓ continuous_const).mem_nhds hx] with y hy
    exact ite_eq_right (not_le.mpr hy)

theorem contDiff_one_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f g : E → F)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : ∀ y, ℓ y = 0 → f y = g y)
    (hder : ∀ y, ℓ y = 0 → fderiv ℝ f y = fderiv ℝ g y) :
    ContDiff ℝ 1 (levelGlue ℓ f g) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨levelGlue ℓ (fderiv ℝ f) (fderiv ℝ g), ?_, ?_⟩
  · exact (hf.continuous_fderiv one_ne_zero).if_le (hg.continuous_fderiv one_ne_zero)
      continuous_const hℓ (fun x hx => hder x hx.symm)
  · intro x
    exact hasFDerivAt_levelGlue ℓ hℓ f g x _ _
      (hf.differentiable one_ne_zero x).hasFDerivAt
      (hg.differentiable one_ne_zero x).hasFDerivAt hval (hder x)

theorem fderiv_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f g : E → F)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hval : ∀ y, ℓ y = 0 → f y = g y)
    (hder : ∀ y, ℓ y = 0 → fderiv ℝ f y = fderiv ℝ g y) (x : E) :
    fderiv ℝ (levelGlue ℓ f g) x = levelGlue ℓ (fderiv ℝ f) (fderiv ℝ g) x :=
  (hasFDerivAt_levelGlue ℓ hℓ f g x _ _ (hf x).hasFDerivAt (hg x).hasFDerivAt
    hval (hder x)).fderiv

theorem contDiff_two_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f g : E → F)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hval : ∀ y, ℓ y = 0 → f y = g y)
    (hder : ∀ y, ℓ y = 0 → fderiv ℝ f y = fderiv ℝ g y)
    (hsec : ∀ y, ℓ y = 0 → fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y) :
    ContDiff ℝ 2 (levelGlue ℓ f g) := by
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (levelGlue ℓ f g)
  apply contDiff_succ_iff_fderiv.mpr
  refine ⟨(contDiff_one_levelGlue ℓ hℓ f g (hf.of_le (by norm_num))
    (hg.of_le (by norm_num)) hval hder).differentiable one_ne_zero, ?_, ?_⟩
  · intro h
    norm_num at h
  · have he : fderiv ℝ (levelGlue ℓ f g) = levelGlue ℓ (fderiv ℝ f) (fderiv ℝ g) :=
      funext (fderiv_levelGlue ℓ hℓ f g (hf.differentiable (by norm_num))
        (hg.differentiable (by norm_num)) hval hder)
    rw [he]
    exact contDiff_one_levelGlue ℓ hℓ _ _ (hf.fderiv_right (by norm_num))
      (hg.fderiv_right (by norm_num)) hder hsec

theorem second_fderiv_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f g : E → F)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hval : ∀ y, ℓ y = 0 → f y = g y)
    (hder : ∀ y, ℓ y = 0 → fderiv ℝ f y = fderiv ℝ g y)
    (hsec : ∀ y, ℓ y = 0 → fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y)
    (x : E) : fderiv ℝ (fderiv ℝ (levelGlue ℓ f g)) x =
      levelGlue ℓ (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ g)) x := by
  have he : fderiv ℝ (levelGlue ℓ f g) = levelGlue ℓ (fderiv ℝ f) (fderiv ℝ g) :=
    funext (fderiv_levelGlue ℓ hℓ f g (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) hval hder)
  rw [he]
  exact fderiv_levelGlue ℓ hℓ _ _ ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero)
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) hder hsec x

end OAI.Analysis.PDE.Schauder
