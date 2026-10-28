import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLattice
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocalLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalBasis
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalCoordinateGluing

/-! # Principal Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrincipalCoordinates.CM

noncomputable section

/-! The literal principal PEL level of the actual filled source matrix
is exactly the marked q-inverted reference lattice level and all retained
integral local blocks. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL.CM.Intrinsic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hb : D.reference.b = B.b)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hstandard : ∀ v, CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice)

include hg hq hstandard b in
theorem principal_iff (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g ∈ D.reference.adelicPrincipalLevel N ↔
      (Matrix.SpecialLinearGroup.toLin' g.val).restrictScalars ℚ ∈
        AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (CMExtraction.LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q).toAddSubgroup N ∧
      ∀ v : Fin s × Bool, v.1 ≠ D.reference.distinguished →
        Matrix.SpecialLinearGroup.map (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) g.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q := by
  have hi : (IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g).val.symm = (IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g⁻¹).val :=
    (congrArg (fun h : D.reference.FiniteSpecialUnitary => h.val) (map_inv (IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb) g)).symm
  have hforward := forall_congr' (fun j => FilledLattice.CM.image_iff E Q D hb hg hq b g (b j).val)
  have hinverse := forall_congr' (fun j =>
    (Iff.of_eq (congrArg (fun f : (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) ≃ₗ[AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E]
      (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => f (CMExtraction.LatticeGenerators.TestTransport.completedVectorBasis E D.reference.lattice b j) ∈
        D.reference.completedLattice) hi)).trans
      (FilledLattice.CM.image_iff E Q D hb hg hq b g⁻¹ (b j).val))
  have hdifference := forall_congr' (fun j =>
    FilledLattice.CM.difference_iff E Q D hb hg hq b g (N : ℚ)⁻¹ (b j).val)
  have hsplit := CMExtraction.PrincipalCoordinateGluing.TestTransport.principal_coordinate_conditions
    (fun j => g.val.val *ᵥ (b j).val ∈ CMExtraction.LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q)
    (fun j => (g⁻¹).val.val *ᵥ (b j).val ∈ CMExtraction.LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q)
    (fun j => (N : ℚ)⁻¹ • (g.val.val *ᵥ (b j).val - (b j).val) ∈
      CMExtraction.LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q) _ _ _
    (FilledLocalLattice.CM.inverse_basis E D hg hq hstandard b g)
    (FilledLocalLattice.CM.difference_basis E D b N hcop g)
  have haway := CMExtraction.PrincipalLatticeDivision.TestTransport.principalPowerLocalizedLattice_iff_basis D.reference.lattice b q N hN
    ((Matrix.SpecialLinearGroup.toLin' g.val).restrictScalars ℚ)
  have hlocal := (FilledLocalLattice.CM.basis_iff E D hg hq hstandard b g).trans
    (FilledLocalLattice.CM.integral_iff E D g)
  exact (CMExtraction.PEL.PrincipalBasis.TestTransport.pelPrincipalLevel_iff_basis E D.reference b N hN (IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g)).trans
    ((and_congr hforward (and_congr hinverse hdifference)).trans
      (hsplit.trans (and_congr haway.symm hlocal)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrincipalCoordinates.CM
