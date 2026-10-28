import OAI.Geometry.Nikodym.Beltrami.Geodesic
import Mathlib.Analysis.Calculus.Deriv.AffineMap

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem beltrami_line_acceleration {κ : ℝ} {x d : E}
    (hq : beltramiDenominator κ x ≠ 0) :
    (2*κ*⟪x,beltramiDenominator κ x • d⟫) • d =
      -beltramiChristoffel κ x (beltramiDenominator κ x • d)
        (beltramiDenominator κ x • d) := by
  simp only [beltramiChristoffel,smul_smul,←add_smul]
  rw [←neg_smul]
  congr 1
  field_simp
  ring

/-- The reciprocal-denominator time change makes a straight line an
affinely parametrized geodesic for the verified Beltrami connection. -/
theorem isBeltramiGeodesic_line_reparam {κ : ℝ} (a b : E) {s : ℝ → ℝ} {I : Set ℝ}
    (hs : ∀ t ∈ I, HasDerivAt s
      (beltramiDenominator κ (AffineMap.lineMap a b (s t))) t)
    (hq : ∀ t ∈ I, 0 < beltramiDenominator κ (AffineMap.lineMap a b (s t))) :
    IsBeltramiGeodesic κ (AffineMap.lineMap a b ∘ s)
      (fun t => beltramiDenominator κ (AffineMap.lineMap a b (s t)) • (b-a)) I := by
  have hpos (t : ℝ) (ht : t ∈ I) : HasDerivAt (AffineMap.lineMap a b ∘ s)
      (beltramiDenominator κ (AffineMap.lineMap a b (s t)) • (b-a)) t :=
    AffineMap.hasDerivAt_lineMap.scomp t (hs t ht)
  refine ⟨hpos,?_,hq⟩
  intro t ht
  have hv := (hasDerivAt_beltramiDenominator (κ:=κ) (hpos t ht)).smul_const (b-a)
  simpa only [Function.comp_apply, beltrami_line_acceleration (hq t ht).ne'] using hv

theorem beltrami_line_reparam_velocity_ne_zero {κ : ℝ} {a b : E}
    (hab : a ≠ b) {s : ℝ → ℝ} {t : ℝ}
    (hq : 0 < beltramiDenominator κ (AffineMap.lineMap a b (s t))) :
    beltramiDenominator κ (AffineMap.lineMap a b (s t)) • (b-a) ≠ 0 :=
  smul_ne_zero hq.ne' (sub_ne_zero.mpr hab.symm)

theorem line_reparam_image {a b : E} {s : ℝ → ℝ} {I : Set ℝ}
    (hs : s '' I = Icc (0 : ℝ) 1) :
    (AffineMap.lineMap a b ∘ s) '' I = segment ℝ a b := by
  rw [image_comp,hs]
  rw [←segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num),image_segment]
  simp

end OAI.Geometry.Nikodym
