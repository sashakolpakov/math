import OAI.Analysis.PDE.Schauder.Calculus.Schauder.FarDerivative

/-! The smooth far contribution is Lipschitz at the scale r^(α−1). -/

noncomputable section
open _root_.MeasureTheory Set
namespace OAI.Analysis.PDE.Schauder

theorem farConvolution_difference_bound {m : ℕ} (hm : 1 ≤ m) (v w : EuclideanSpace ℝ (Fin m)) :
    ∃ C > 0, ∀ (r α H : ℝ), 0 < r → α < 1 → 0 ≤ H →
      ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      |scalarConvolution (truncatedNewtonianEntry m v w r) f z -
        scalarConvolution (truncatedNewtonianEntry m v w r) f x| ≤
        (H * C * (r / 2) ^ (α - 1) * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α) * ‖z - x‖ := by
  obtain ⟨C, hC, hbound⟩ := farConvolution_fderiv_bound hm v w
  refine ⟨C, hC, ?_⟩
  intro r α H hr hα hH f hf hfc hh x z
  have hF : ContDiff ℝ 1 (scalarConvolution (truncatedNewtonianEntry m v w r) f) :=
    contDiff_scalarConvolution _ f (contDiff_truncatedNewtonianEntry m v w hr).continuous.locallyIntegrable hf hfc
  have hb (a : EuclideanSpace ℝ (Fin m)) (_ha : a ∈ (univ : Set (EuclideanSpace ℝ (Fin m)))) :
      ‖fderiv ℝ (scalarConvolution (truncatedNewtonianEntry m v w r) f) a‖ ≤
        H * C * (r / 2) ^ (α - 1) * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α := by
    apply hbound r α H hr hα hH f hf hfc a
    intro y
    have he : a - y - a = -y := by abel
    simpa only [he, norm_neg] using hh (a - y) a
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun a _ => hF.differentiable one_ne_zero a) hb (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℝ (Fin m))))
    (mem_univ x) (mem_univ z)

end OAI.Analysis.PDE.Schauder
