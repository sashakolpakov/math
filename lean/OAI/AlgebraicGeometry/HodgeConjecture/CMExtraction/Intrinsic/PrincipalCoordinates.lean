import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalCongruence
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalBasis
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalCoordinateGluing

/-! # Principal Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalCoordinates.ParameterChoices

noncomputable section

/-! The literal principal PEL subgroup of the actual filled native
element is exactly the original marked away lattice level together
with integral blocks at every non-active split slot. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hstandard : ∀ v, SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
  {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ D.reference.lattice] (b : Module.Basis J ℤ D.reference.lattice)

include hq hstandard b in
theorem nativeFilledPEL_principal_iff (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) :
    FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ ∈ D.reference.adelicPrincipalLevel N ↔
      (Matrix.SpecialLinearGroup.toLin' γ.val).restrictScalars ℚ ∈
        AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q).toAddSubgroup N ∧
      ∀ v : Fin s × Bool, v.1 ≠ D.reference.distinguished →
        Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) γ.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q := by
  have hi : (FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val.symm = (FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ⁻¹).val :=
    (congrArg (fun g : D.reference.FiniteSpecialUnitary => g.val)
      (map_inv (FilledPEL.ParameterChoices.nativeFilledPEL E D hg) γ)).symm
  have hforward := forall_congr' (fun j => FilledLattice.ParameterChoices.nativeFilledPEL_lattice_image_iff E D hg hq b γ (b j).val)
  have hinverse := forall_congr' (fun j =>
    (Iff.of_eq (congrArg (fun f : (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) ≃ₗ[AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E]
        (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => f (LatticeGenerators.TestTransport.completedVectorBasis E D.reference.lattice b j) ∈
          D.reference.completedLattice) hi)).trans
      (FilledLattice.ParameterChoices.nativeFilledPEL_lattice_image_iff E D hg hq b γ⁻¹ (b j).val))
  have hdifference := forall_congr' (fun j =>
    FilledLattice.ParameterChoices.nativeFilledPEL_lattice_difference_iff E D hg hq b γ (N : ℚ)⁻¹ (b j).val)
  have hsplit := PrincipalCoordinateGluing.TestTransport.principal_coordinate_conditions
    (fun j => γ.val.val *ᵥ (b j).val ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q)
    (fun j => (γ⁻¹).val.val *ᵥ (b j).val ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q)
    (fun j => (N : ℚ)⁻¹ • (γ.val.val *ᵥ (b j).val - (b j).val) ∈
      LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q) _ _ _
    (LocalCongruence.ParameterChoices.nativeFilledBlocks_inverse_basis E D hg hq hstandard b γ)
    (LocalCongruence.ParameterChoices.nativeFilledBlocks_difference_basis E D b N hcop γ)
  have haway := PrincipalLatticeDivision.TestTransport.principalPowerLocalizedLattice_iff_basis D.reference.lattice b q N hN
    ((Matrix.SpecialLinearGroup.toLin' γ.val).restrictScalars ℚ)
  have hlocal := (LocalBlocks.ParameterChoices.nativeFilledBlocks_basis_iff E D hg hq hstandard b γ).trans
    (LocalBlocks.ParameterChoices.nativeFilledBlocks_integral_iff E D γ)
  exact (PEL.PrincipalBasis.TestTransport.pelPrincipalLevel_iff_basis E D.reference b N hN (FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ)).trans
    ((and_congr hforward (and_congr hinverse hdifference)).trans
      (hsplit.trans (and_congr haway.symm hlocal)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalCoordinates.ParameterChoices
