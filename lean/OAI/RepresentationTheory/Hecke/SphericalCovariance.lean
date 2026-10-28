import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke
import OAI.RepresentationTheory.Hecke.SphericalActionModelInverse
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Spherical Covariance -/

namespace OAI.RepresentationTheory.Hecke.SphericalCovariance.ActionIntrinsic

noncomputable section

/-! The local symplectic projection of the actual GeometricTheta splitting determines
its radial Hecke action. All formulas use GeometricTheta's spherical input space and
finite Weil operators, with the original raw normalization. -/

open scoped TensorProduct
open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)

theorem native_spherical_auxiliary_hecke
    (hs : D.splitting.comp (MonoidHom.inl (Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u)
    (φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (J : RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs)
    (hJ : ∀ b, (J b).val = AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)
    (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RadialDilation.Cm.radialInput q) :
    D.sphericalWeil T (J b) = J (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action.sphericalRadialAction q (AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphismAction.Local.contragredientHecke q T) b) := by
  have hρ : D.finiteWeil.comp (MonoidHom.inl (Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u := by
    change D.weil.finite.action.comp (D.splitting.comp (MonoidHom.inl _ _)) = _
    rw [hs]
    rfl
  apply Subtype.ext
  change Theta.Geometric.SphericalGU.Spherical.weilOperator (Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (D.finiteWeil.comp (MonoidHom.inl (Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga)) T (J b).val =
      (J (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action.sphericalRadialAction q (AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphismAction.Local.contragredientHecke q T) b)).val
  rw [hJ, hJ, hρ]
  exact AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinate_dual_hecke q D.pel.reference.distinguished D.weil u φ c T b

theorem native_spherical_auxiliary_complex
    (hs : D.splitting.comp (MonoidHom.inl (Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u)
    (φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (J : RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs)
    (hJ : ∀ b, (J b).val = AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)
    (hElementaryDivisors : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (T : ℂ ⊗[ℚ] Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RadialDilation.Cm.radialInput q) :
    D.sphericalWeilComplex T (J b) = J (AlgebraicGeometry.HodgeConjecture.CMExtraction.ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) := by
  induction T using TensorProduct.inductionOn with
  | add T U hT hU => simp only [map_add, LinearMap.add_apply, hT, hU]
  | tmul z T =>
      change z • D.sphericalWeil T (J b) =
        J (z • AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action.sphericalRadialAction q (AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphismAction.Local.contragredientHecke q T) b)
      rw [map_smul, native_spherical_auxiliary_hecke D c u hs φ J hJ]

end

end OAI.RepresentationTheory.Hecke.SphericalCovariance.ActionIntrinsic
