import OAI.Geometry.Nikodym.Jacobi.Normal

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace SmoothCoordinateMetric

variable (g : SmoothCoordinateMetric E)

omit [FiniteDimensional ℝ E] in
theorem metric_inner_comm {x : E} (hx : x ∈ g.domain) (u v : E) :
    g.inner x u v = g.inner x v u := by
  exact (g.symmetric x hx u v).trans (real_inner_comm _ _)

omit [FiniteDimensional ℝ E] in
theorem inner_sub_projections {x : E} (hx : x ∈ g.domain) (u w v : E) (a b : ℝ)
    (hv : g.inner x v v = 1) (ha : g.inner x u v = a) (hb : g.inner x w v = b) :
    g.inner x (u-a•v) (w-b•v) = g.inner x u w - a*b := by
  have hc : g.inner x v w = b := (g.metric_inner_comm hx v w).trans hb
  simp only [SmoothCoordinateMetric.inner,map_sub,map_smul,inner_sub_left,inner_sub_right,
    real_inner_smul_left,inner_smul_right] at hv ha hb hc ⊢
  rw [ha,hv,hc]
  ring

end SmoothCoordinateMetric

namespace IsUnitJacobiField

variable {g : SmoothCoordinateMetric E} {κ : ℝ} {γ v J A : ℝ → E} {I : Set ℝ}

def transversePosition (g : SmoothCoordinateMetric E) (γ v J A : ℝ → E) (t : ℝ) : E :=
  J t - (t * g.inner (γ 0) (A 0) (v 0)) • v t

def transverseVelocity (g : SmoothCoordinateMetric E) (γ v A : ℝ → E) (t : ℝ) : E :=
  A t - g.inner (γ 0) (A 0) (v 0) • v t

theorem transverse_equations (h : IsUnitJacobiField g κ γ v J A I)
    (hγ : IsMetricGeodesic g γ v I) (hI : Convex ℝ I) (h0 : 0 ∈ I)
    (hunit : ∀ t ∈ I, g.inner (γ t) (v t) (v t) = 1)
    (hJ0 : J 0 = 0) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (IsUnitJacobiField.transversePosition g γ v J A)
      (IsUnitJacobiField.transverseVelocity g γ v A t -
        g.christoffel (γ t) (v t) (IsUnitJacobiField.transversePosition g γ v J A t)) t ∧
    HasDerivAt (IsUnitJacobiField.transverseVelocity g γ v A)
      ((-κ) • IsUnitJacobiField.transversePosition g γ v J A t -
        g.christoffel (γ t) (v t) (IsUnitJacobiField.transverseVelocity g γ v A t)) t := by
  let b := g.inner (γ 0) (A 0) (v 0)
  have hp := (h.radial_pairings hγ hI h0 hunit hJ0 ht).2
  constructor
  · have hd := (h.position_derivative t ht).sub
      (((hasDerivAt_id t).mul_const b).smul (hγ.velocity_derivative t ht))
    convert hd using 1
    · rfl
    · change A t - b • v t - (g.christoffelBilinear (γ t) (v t))
        (J t - (t*b) • v t) = _
      simp only [map_sub,map_smul,OAI.Geometry.Nikodym.SmoothCoordinateMetric.christoffelBilinear_apply,id_eq]
      module
  · have hd := (h.velocity_derivative t ht).sub ((hγ.velocity_derivative t ht).const_smul b)
    convert hd using 1
    · rfl
    · change (-κ) • (J t - (t*b) • v t) - (g.christoffelBilinear (γ t) (v t))
        (A t - b • v t) = _
      simp only [map_sub,map_smul,OAI.Geometry.Nikodym.SmoothCoordinateMetric.christoffelBilinear_apply]
      rw [hp]
      dsimp [b]
      module

theorem normal_metric {J₁ A₁ J₂ A₂ : ℝ → E}
    (h1 : IsUnitJacobiField g κ γ v J₁ A₁ I)
    (h2 : IsUnitJacobiField g κ γ v J₂ A₂ I)
    (hγ : IsMetricGeodesic g γ v I) (hI : Convex ℝ I) (h0 : 0 ∈ I)
    (hunit : ∀ t ∈ I, g.inner (γ t) (v t) (v t) = 1)
    (h10 : J₁ 0 = 0) (h20 : J₂ 0 = 0) {t : ℝ} (ht : t ∈ I) :
    g.inner (γ t) (J₁ t) (J₂ t) =
      t^2 * (g.inner (γ 0) (A₁ 0) (v 0) * g.inner (γ 0) (A₂ 0) (v 0)) +
      (curvatureSin κ t)^2 * (g.inner (γ 0) (A₁ 0) (A₂ 0) -
        g.inner (γ 0) (A₁ 0) (v 0) * g.inner (γ 0) (A₂ 0) (v 0)) := by
  have e1 (s : ℝ) (hs : s ∈ I) := h1.transverse_equations hγ hI h0 hunit h10 hs
  have e2 (s : ℝ) (hs : s ∈ I) := h2.transverse_equations hγ hI h0 hunit h20 hs
  have hm := g.covariant_oscillator_inner hI h0 κ hγ.regular hγ.position_derivative
    (fun s hs => (e1 s hs).1) (fun s hs => (e1 s hs).2)
    (fun s hs => (e2 s hs).1) (fun s hs => (e2 s hs).2)
    (by simp [IsUnitJacobiField.transversePosition,h10]) (by simp [IsUnitJacobiField.transversePosition,h20]) ht
  have hleft := g.inner_sub_projections (hγ.regular t ht) (J₁ t) (J₂ t) (v t)
    _ _ (hunit t ht) (h1.radial_pairings hγ hI h0 hunit h10 ht).2
    (h2.radial_pairings hγ hI h0 hunit h20 ht).2
  have hright := g.inner_sub_projections (hγ.regular 0 h0) (A₁ 0) (A₂ 0) (v 0)
    _ _ (hunit 0 h0) rfl rfl
  dsimp only [IsUnitJacobiField.transversePosition,IsUnitJacobiField.transverseVelocity] at hm
  rw [hleft,hright] at hm
  calc
    g.inner (γ t) (J₁ t) (J₂ t) =
      (curvatureSin κ t)^2 * (g.inner (γ 0) (A₁ 0) (A₂ 0) -
        g.inner (γ 0) (A₁ 0) (v 0) * g.inner (γ 0) (A₂ 0) (v 0)) +
      (t * g.inner (γ 0) (A₁ 0) (v 0)) * (t * g.inner (γ 0) (A₂ 0) (v 0)) := by linarith
    _ = _ := by ring

end IsUnitJacobiField
end OAI.Geometry.Nikodym
