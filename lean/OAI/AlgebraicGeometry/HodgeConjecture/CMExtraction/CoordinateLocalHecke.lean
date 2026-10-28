import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalHecke
import OAI.RepresentationTheory.Hecke.RadialDilation.ConcreteFinite

/-! # Coordinate Local Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateLocalHecke

noncomputable section

/-! The exact local action and radial Hecke comparison in the same finite
coordinates and auxiliary vector used by the native RadialDilation dilation. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization
open scoped Classical _root_.Matrix

theorem weilOperator_intertwines {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (K : Subgroup G) (ρ : G →* (V ≃ₗ[ℂ] V)) (τ : G →* (W ≃ₗ[ℂ] W))
    (L : V →ₗ[ℂ] W) (h : ∀ g v, L (ρ g v) = τ g (L v))
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) (v : V) :
    L (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ T v) = RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K τ T (L v) := by
  simp only [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator, Finsupp.sum, LinearMap.sum_apply,
    map_sum, LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h]

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (u : MpF)

def coordinateActiveLift : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF :=
  (MulAut.conj u⁻¹).toMonoidHom.comp (ActiveLocalLift.activeFiniteLift q e μ D)

def coordinateActiveRepresentation : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :=
  D.finite.action.comp (coordinateActiveLift q e μ D u)

theorem coordinateActiveLift_projection (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    D.finite.project (coordinateActiveLift q e μ D u g) =
      (D.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (ActiveBlockMatrices.Local.activeBlockGL e μ g)) *
        D.finite.project u := by
  change D.finite.project (u⁻¹ * ActiveLocalLift.activeFiniteLift q e μ D g * (u⁻¹)⁻¹) = _
  rw [inv_inv, map_mul, map_mul, map_inv, ActiveLocalLift.activeFiniteLift_projection]

theorem coordinateActive_action (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :
    coordinateActiveRepresentation q e μ D u g (D.finite.action u⁻¹ f) =
      D.finite.action u⁻¹ (ActiveLocalHecke.activeFiniteRepresentation q e μ D g f) := by
  change D.finite.action (u⁻¹ * ActiveLocalLift.activeFiniteLift q e μ D g * (u⁻¹)⁻¹)
    (D.finite.action u⁻¹ f) = D.finite.action u⁻¹ (D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D g) f)
  rw [inv_inv]
  rw [← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem coordinateRadial_active_fixed (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q μ D u b ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (coordinateActiveRepresentation q e μ D u) := by
  intro g hg
  change coordinateActiveRepresentation q e μ D u g
    (D.finite.action u⁻¹ (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)) = _
  rw [coordinateActive_action, ActiveLocalHecke.canonicalRadial_active_fixed q e μ D b g hg]
  rfl

def coordinateRadialFixedEmbedding : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (coordinateActiveRepresentation q e μ D u) :=
  (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q μ D u).codRestrict _ (coordinateRadial_active_fixed q e μ D u)

theorem coordinateRadial_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (coordinateActiveRepresentation q e μ D u) T
      (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q μ D u b) =
        RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q μ D u (Radial.Action.sphericalRadialAction q T b) := by
  have h := weilOperator_intertwines (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (ActiveLocalHecke.activeFiniteRepresentation q e μ D) (coordinateActiveRepresentation q e μ D u)
    (D.finite.action u⁻¹).toLinearMap (fun g f => (coordinateActive_action q e μ D u g f).symm)
    T (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)
  rw [ActiveLocalHecke.activeRadial_hecke] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateLocalHecke
