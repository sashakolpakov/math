import OAI.Geometry.Nikodym.CovariantOscillator
import OAI.Geometry.Nikodym.MetricGeodesic
import OAI.Geometry.Nikodym.Jacobi.Variation

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A Jacobi field and its covariant velocity along a unit-speed geodesic
of a space form, given by the actual coordinate covariant equations. -/
structure IsUnitJacobiField (g : SmoothCoordinateMetric E) (κ : ℝ)
    (γ v J A : ℝ → E) (I : Set ℝ) : Prop where
  position_derivative : ∀ t ∈ I,
    HasDerivAt J (A t - g.christoffel (γ t) (v t) (J t)) t
  velocity_derivative : ∀ t ∈ I,
    HasDerivAt A ((-κ) • (J t - g.inner (γ t) (J t) (v t) • v t) -
      g.christoffel (γ t) (v t) (A t)) t

namespace IsUnitJacobiField

variable {g : SmoothCoordinateMetric E} {κ : ℝ} {γ v J A : ℝ → E} {I : Set ℝ}

theorem hasDerivAt_radial_pairing (h : IsUnitJacobiField g κ γ v J A I)
    (hγ : IsMetricGeodesic g γ v I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => g.inner (γ s) (J s) (v s))
      (g.inner (γ t) (A t) (v t)) t := by
  simpa only [sub_add_cancel,neg_add_cancel,OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,
    inner_zero_right,add_zero] using
    g.hasDerivAt_inner_covariant (hγ.regular t ht) (hγ.position_derivative t ht)
      (h.position_derivative t ht) (hγ.velocity_derivative t ht)

theorem hasDerivAt_radial_velocity (h : IsUnitJacobiField g κ γ v J A I)
    (hγ : IsMetricGeodesic g γ v I) {t : ℝ} (ht : t ∈ I)
    (hunit : g.inner (γ t) (v t) (v t) = 1) :
    HasDerivAt (fun s => g.inner (γ s) (A s) (v s)) 0 t := by
  have hd := g.hasDerivAt_inner_covariant (hγ.regular t ht) (hγ.position_derivative t ht)
      (h.velocity_derivative t ht) (hγ.velocity_derivative t ht)
  convert hd using 1
  simp only [sub_add_cancel,neg_add_cancel,OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,
    map_smul,map_sub,inner_zero_right,add_zero,real_inner_smul_left,inner_sub_left]
  change 0 = -κ * (g.inner (γ t) (J t) (v t) -
    g.inner (γ t) (J t) (v t) * g.inner (γ t) (v t) (v t))
  rw [hunit,mul_one,sub_self,mul_zero]

theorem radial_pairings (h : IsUnitJacobiField g κ γ v J A I)
    (hγ : IsMetricGeodesic g γ v I) (hI : Convex ℝ I) (h0 : 0 ∈ I)
    (hunit : ∀ t ∈ I, g.inner (γ t) (v t) (v t) = 1)
    (hJ0 : J 0 = 0) {t : ℝ} (ht : t ∈ I) :
    g.inner (γ t) (A t) (v t) = g.inner (γ 0) (A 0) (v 0) ∧
    g.inner (γ t) (J t) (v t) = t * g.inner (γ 0) (A 0) (v 0) := by
  have hA (s : ℝ) (hs : s ∈ I) :
      g.inner (γ s) (A s) (v s) = g.inner (γ 0) (A 0) (v 0) :=
    eq_of_hasDerivAt_zero_on_convex hI
      (fun r hr => h.hasDerivAt_radial_velocity hγ hr (hunit r hr)) h0 hs
  refine ⟨hA t ht,?_⟩
  have hd (s : ℝ) (hs : s ∈ I) :
      HasDerivAt (fun r => g.inner (γ r) (J r) (v r) -
        r * g.inner (γ 0) (A 0) (v 0)) 0 s := by
    convert (h.hasDerivAt_radial_pairing hγ hs).sub
      ((hasDerivAt_id s).mul_const (g.inner (γ 0) (A 0) (v 0))) using 1
    · rfl
    · simp only [hA s hs,one_mul,sub_self]
  have he := eq_of_hasDerivAt_zero_on_convex hI hd h0 ht
  simpa only [hJ0,OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,map_zero,inner_zero_left,
    zero_mul,sub_zero,sub_eq_zero] using he

end IsUnitJacobiField

theorem IsMetricGeodesic.unitJacobiField_of_linearized
    {g : SmoothCoordinateMetric E} {κ : ℝ} {γ v J U : ℝ → E} {I : Set ℝ}
    (h : IsMetricGeodesic g γ v I) (hκ : g.HasConstantCurvature κ)
    (hunit : ∀ t ∈ I, g.inner (γ t) (v t) (v t) = 1)
    (hJ : ∀ t ∈ I, HasDerivAt J (U t) t)
    (hU : ∀ t ∈ I, HasDerivAt U
      (-(fderiv ℝ (fun x => g.christoffel x (v t) (v t)) (γ t) (J t) +
        g.christoffel (γ t) (U t) (v t) + g.christoffel (γ t) (v t) (U t))) t) :
    IsUnitJacobiField g κ γ v J (g.variationVelocity γ v J U) I := by
  constructor
  · intro t ht
    simpa only [OAI.Geometry.Nikodym.SmoothCoordinateMetric.variationVelocity,add_sub_cancel_right] using hJ t ht
  · intro t ht
    simpa only [hunit t ht,one_smul,neg_smul] using
      g.hasDerivAt_variationVelocity_spaceForm hκ (h.regular t ht)
        (h.position_derivative t ht) (h.velocity_derivative t ht) (hJ t ht) (hU t ht)

end OAI.Geometry.Nikodym
