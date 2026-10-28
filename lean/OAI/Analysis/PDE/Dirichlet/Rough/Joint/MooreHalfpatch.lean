import OAI.Analysis.PDE.Dirichlet.Rough.Joint.Halfpatch
import OAI.Analysis.PDE.Dirichlet.NonlinearParameterMoore

noncomputable section
open Set
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace
attribute [local instance] residualFirstGroup residualFirstSpace
  residualSecondGroup residualSecondSpace

variable {m n : ℕ} {Z E : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "W" => EuclideanSpace ℝ (Fin m)
local notation "Phys" => CoordinateSpace n 4

/-- For the actual parameter-dependent Moore equation, positivity of the
spatial quaternionic Hessian supplies the normal-symbol condition. -/
theorem exists_smooth_joint_moore_halfpatch
    (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ)
    (Bg : Z × E → Phys →L[ℝ] Phys →L[ℝ] ℝ)
    (J : Z × E → Phys →L[ℝ] E)
    (T : Z × E → Phys →L[ℝ] Phys →L[ℝ] E) (load : Z × E → ℝ)
    (hBg : ContDiff ℝ ∞ Bg) (hJ : ContDiff ℝ ∞ J)
    (hT : ContDiff ℝ ∞ T) (hload : ContDiff ℝ ∞ load)
    (ν : W) (hν : (k.comp (reindexSpatialProjection e)) ν = 1)
    {O : Set W} (hO : IsOpen O) {S : Set (Z × E)}
    {f : Z × E → ℝ} {g : W → ℝ} (hg : ContDiff ℝ 2 g)
    (hext : EqOn g (f ∘ e) ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O))
    (hmaps : MapsTo e ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O) S)
    (hi : ∀ x ∈ O, 0 < (k.comp (reindexSpatialProjection e)) x → ContDiffAt ℝ ∞ g x)
    (hmixed : ∀ (N : ℕ) (v : Fin N → Z × k.ker),
      ContDiffOn ℝ 2 (fun p : Z × E ↦ iteratedFDeriv ℝ N
        (fun t : Z × k.ker ↦ f (p.1+t.1,p.2+(t.2:E))) 0 v) S)
    (honto : ∀ x ∈ ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O),
      Function.Surjective (J (e x)))
    (hpositive : ∀ x ∈ ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O),
      (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg (e x)) (J (e x)) (T (e x))
        (spatialGradientRestriction (reindexSpatialInclusion e) (fderiv ℝ g x))
        (spatialHessianRestriction (reindexSpatialInclusion e) (fderiv ℝ (fderiv ℝ g) x)))).PosDef)
    (heq : ∀ x ∈ ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O),
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg (e x)) (J (e x)) (T (e x))
        (spatialGradientRestriction (reindexSpatialInclusion e) (fderiv ℝ g x))
        (spatialHessianRestriction (reindexSpatialInclusion e) (fderiv ℝ (fderiv ℝ g) x))) = load (e x))
    {x₀ : W} (hx₀ : x₀ ∈ O) (hxk : (k.comp (reindexSpatialProjection e)) x₀ = 0) :
    ∃ V : Set W, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ O ∧
      ∃ u : W → ℝ, ContDiff ℝ ∞ u ∧
        EqOn u (f ∘ e) ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ V) := by
  have hF := contDiff_parameterMooreResidual hBg hJ hT hload
  have hk : k ≠ 0 := by
    intro hk
    have hbad : (0:ℝ) = 1 := by
      simpa only [hk,ContinuousLinearMap.zero_comp,zero_apply] using hν
    exact zero_ne_one hbad
  apply exists_smooth_joint_halfpatch_representative e k
    (parameterMooreResidual Bg J T load) hF ν hν hO hg hext hmaps hi hmixed
    ?_ ?_ hx₀ hxk
  · intro x hx
    change OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg (e x)) (J (e x)) (T (e x))
      (spatialGradientRestriction (reindexSpatialInclusion e) (fderiv ℝ g x))
      (spatialHessianRestriction (reindexSpatialInclusion e) (fderiv ℝ (fderiv ℝ g) x))) - load (e x) = 0
    exact sub_eq_zero.mpr (heq x hx)
  · intro x hx
    apply ne_of_gt
    apply parameterMooreResidual_slice_normal_pos _ _ k hk
    · exact honto x hx
    · exact hpositive x hx
    · exact (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _

end OAI.Analysis.PDE.Dirichlet
