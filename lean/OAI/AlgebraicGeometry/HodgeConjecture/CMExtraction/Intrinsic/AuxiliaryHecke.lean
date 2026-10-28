import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Spectrum
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Auxiliary Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryHecke

noncomputable section

/-! The local symplectic projection of the actual GeometricTheta splitting determines
its radial Hecke action. All formulas use GeometricTheta's spherical input space and
finite Weil operators, with the original raw normalization. -/

open scoped TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)

theorem native_spherical_auxiliary_hecke
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (J : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs)
    (hJ : ∀ b, (J b).val = AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    D.sphericalWeil T (J b) = J (Radial.Action.sphericalRadialAction q (HeckeAutomorphismAction.Local.contragredientHecke q T) b) := by
  have hρ : D.finiteWeil.comp (MonoidHom.inl (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga) =
      CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u := by
    change D.weil.finite.action.comp (D.splitting.comp (MonoidHom.inl _ _)) = _
    rw [SphericalRadial.native_local_splitting_eq_dual D c u hp]
    rfl
  apply Subtype.ext
  change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (D.finiteWeil.comp (MonoidHom.inl (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga)) T (J b).val =
      (J (Radial.Action.sphericalRadialAction q (HeckeAutomorphismAction.Local.contragredientHecke q T) b)).val
  rw [hJ, hJ, hρ]
  exact AuxiliaryCoordinate.Local.auxiliaryCoordinate_dual_hecke q D.pel.reference.distinguished D.weil u φ c T b

theorem native_spherical_auxiliary_complex
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (J : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs)
    (hJ : ∀ b, (J b).val = AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    D.sphericalWeilComplex T (J b) = J (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) := by
  induction T using TensorProduct.inductionOn with
  | add T U hT hU => simp only [map_add, LinearMap.add_apply, hT, hU]
  | tmul z T =>
      change z • D.sphericalWeil T (J b) =
        J (z • Radial.Action.sphericalRadialAction q (HeckeAutomorphismAction.Local.contragredientHecke q T) b)
      rw [map_smul, native_spherical_auxiliary_hecke D c u hp φ J hJ]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryHecke
