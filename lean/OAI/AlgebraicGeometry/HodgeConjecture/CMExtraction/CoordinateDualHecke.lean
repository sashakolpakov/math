import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ContragredientRadial

/-! # Coordinate Dual Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local

noncomputable section

/-! Exact radial action for the inverse-transpose block in the native
finite symplectic coordinates. The lift is determined by its projection. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open scoped Classical

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (u : MpF)

def coordinateDualLift : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF :=
  (CoordinateLocalHecke.coordinateActiveLift q e μ D u).comp (Contragredient.Local.contragredient ℚ_[q])

def coordinateDualRepresentation : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :=
  D.finite.action.comp (coordinateDualLift q e μ D u)

theorem coordinateDualLift_projection (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    D.finite.project (coordinateDualLift q e μ D u g) =
      (D.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL e μ (Contragredient.Local.contragredient ℚ_[q] g))) * D.finite.project u :=
  CoordinateLocalHecke.coordinateActiveLift_projection q e μ D u _

theorem coordinateDualLift_unique (f : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF)
    (hf : ∀ g, D.finite.project (f g) =
      (D.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL e μ (Contragredient.Local.contragredient ℚ_[q] g))) * D.finite.project u) :
    f = coordinateDualLift q e μ D u :=
  Finite.Sl.Local.finite_sl3_lift_unique q D f (coordinateDualLift q e μ D u)
    (fun g => (hf g).trans (coordinateDualLift_projection q e μ D u g).symm)

theorem coordinateRadial_dual_fixed (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q μ D u b ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (coordinateDualRepresentation q e μ D u) := by
  intro g hg
  exact CoordinateLocalHecke.coordinateRadial_active_fixed q e μ D u b (Contragredient.Local.contragredient ℚ_[q] g)
    ((Contragredient.Local.contragredient_integral_iff q g).mpr hg)

theorem coordinateRadial_dual_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (coordinateDualRepresentation q e μ D u) T
      (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q μ D u b) =
        RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q μ D u (Radial.Action.sphericalRadialAction q (HeckeAutomorphismAction.Local.contragredientHecke q T) b) := by
  have h := HeckeAutomorphismAction.Local.weilOperator_automorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
    (Contragredient.Local.contragredient_integral_iff q) (CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u)
    (CoordinateLocalHecke.coordinateRadialFixedEmbedding q e μ D u b) T
  exact h.symm.trans (CoordinateLocalHecke.coordinateRadial_hecke q e μ D u (HeckeAutomorphismAction.Local.contragredientHecke q T) b)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local
