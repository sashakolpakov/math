import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialPower
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke

/-! # Auxiliary Coordinate -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local

noncomputable section

/-! Radial tensors with arbitrary auxiliary tests in a fixed finite
coordinate lift. Their injectivity and Hecke action are derived. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  (μ : Place) {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (u : MpF)
  (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ))

def auxiliaryCoordinateRadialEmbedding : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) :=
  (D.finite.action u⁻¹).toLinearMap.comp (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ)

theorem auxiliaryCoordinateRadialEmbedding_injective (hφ : φ ≠ 0) :
    Function.Injective (auxiliaryCoordinateRadialEmbedding q μ D u φ) :=
  (D.finite.action u⁻¹).injective.comp (RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding.Realization.finiteRadialEmbedding_injective q
    (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ) φ.val φ.property.1 φ.property.2 (fun h => hφ (Subtype.ext h)))

variable {n : ℕ} (e : (Place × Fin 3) ≃ Fin n)

theorem auxiliaryCoordinate_active_fixed (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    auxiliaryCoordinateRadialEmbedding q μ D u φ b ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u) := by
  intro g hg
  change CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u g
    (D.finite.action u⁻¹ (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b)) = _
  rw [CoordinateLocalHecke.coordinateActive_action, AuxiliaryRadialHecke.Local.auxiliaryRadial_active_fixed q e μ D φ b g hg]
  rfl

theorem auxiliaryCoordinate_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u) T
      (auxiliaryCoordinateRadialEmbedding q μ D u φ b) =
        auxiliaryCoordinateRadialEmbedding q μ D u φ (Radial.Action.sphericalRadialAction q T b) := by
  have h := CoordinateLocalHecke.weilOperator_intertwines (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (ActiveLocalHecke.activeFiniteRepresentation q e μ D) (CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u)
    (D.finite.action u⁻¹).toLinearMap (fun g f => (CoordinateLocalHecke.coordinateActive_action q e μ D u g f).symm)
    T (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b)
  rw [AuxiliaryRadialHecke.Local.auxiliaryRadial_hecke] at h
  exact h.symm

theorem auxiliaryCoordinate_dual_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (CoordinateDualHecke.Local.coordinateDualRepresentation q e μ D u) T
      (auxiliaryCoordinateRadialEmbedding q μ D u φ b) =
        auxiliaryCoordinateRadialEmbedding q μ D u φ (Radial.Action.sphericalRadialAction q (HeckeAutomorphismAction.Local.contragredientHecke q T) b) := by
  let f : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u) :=
    ⟨auxiliaryCoordinateRadialEmbedding q μ D u φ b, auxiliaryCoordinate_active_fixed q μ D u φ e b⟩
  have h := HeckeAutomorphismAction.Local.weilOperator_automorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
    (Contragredient.Local.contragredient_integral_iff q) (CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u) f T
  exact h.symm.trans (auxiliaryCoordinate_hecke q μ D u φ e (HeckeAutomorphismAction.Local.contragredientHecke q T) b)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local
