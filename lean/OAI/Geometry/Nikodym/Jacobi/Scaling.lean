import OAI.Geometry.Nikodym.Jacobi.Metric

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The genuine space-form Jacobi equation for an arbitrary affine speed. -/
structure IsSpaceFormJacobiField (g : SmoothCoordinateMetric E) (κ : ℝ)
    (γ v J A : ℝ → E) (I : Set ℝ) : Prop where
  position_derivative : ∀ t ∈ I,
    HasDerivAt J (A t - g.christoffel (γ t) (v t) (J t)) t
  velocity_derivative : ∀ t ∈ I,
    HasDerivAt A ((-κ) • (g.inner (γ t) (v t) (v t) • J t -
      g.inner (γ t) (J t) (v t) • v t) - g.christoffel (γ t) (v t) (A t)) t

theorem IsMetricGeodesic.spaceFormJacobiField_of_linearized
    {g : SmoothCoordinateMetric E} {κ : ℝ} {γ v J U : ℝ → E} {I : Set ℝ}
    (h : IsMetricGeodesic g γ v I) (hκ : g.HasConstantCurvature κ)
    (hJ : ∀ t ∈ I, HasDerivAt J (U t) t)
    (hU : ∀ t ∈ I, HasDerivAt U
      (-(fderiv ℝ (fun x => g.christoffel x (v t) (v t)) (γ t) (J t) +
        g.christoffel (γ t) (U t) (v t) + g.christoffel (γ t) (v t) (U t))) t) :
    IsSpaceFormJacobiField g κ γ v J (g.variationVelocity γ v J U) I := by
  constructor
  · intro t ht
    simpa only [OAI.Geometry.Nikodym.SmoothCoordinateMetric.variationVelocity,add_sub_cancel_right] using hJ t ht
  · intro t ht
    simpa only [neg_smul] using
      g.hasDerivAt_variationVelocity_spaceForm hκ (h.regular t ht)
        (h.position_derivative t ht) (h.velocity_derivative t ht) (hJ t ht) (hU t ht)

namespace IsSpaceFormJacobiField

variable {g : SmoothCoordinateMetric E} {κ : ℝ} {γ v J A : ℝ → E} {I : Set ℝ}

theorem unit (h : IsSpaceFormJacobiField g κ γ v J A I)
    (hunit : ∀ t ∈ I, g.inner (γ t) (v t) (v t) = 1) :
    IsUnitJacobiField g κ γ v J A I := by
  refine ⟨h.position_derivative,?_⟩
  intro t ht
  simpa only [hunit t ht,one_smul] using h.velocity_derivative t ht

theorem scale_time (h : IsSpaceFormJacobiField g κ γ v J A I) (a : ℝ) :
    IsSpaceFormJacobiField g κ (fun t => γ (a*t)) (fun t => a • v (a*t))
      (fun t => J (a*t)) (fun t => a • A (a*t)) {t | a*t ∈ I} := by
  constructor
  · intro t ht
    have hd : HasDerivAt (fun s : ℝ => a*s) a t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul a
    have hh := (h.position_derivative _ ht).scomp t hd
    convert hh using 1
    · rfl
    · simp only [g.christoffel_smul_left,smul_sub]
  · intro t ht
    have hd : HasDerivAt (fun s : ℝ => a*s) a t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul a
    have hh := ((h.velocity_derivative _ ht).scomp t hd).const_smul a
    convert hh using 1
    · rfl
    · simp only [OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,map_smul,real_inner_smul_left,
        inner_smul_right,g.christoffel_smul_left,g.christoffel_smul_right]
      module

end IsSpaceFormJacobiField
end OAI.Geometry.Nikodym
