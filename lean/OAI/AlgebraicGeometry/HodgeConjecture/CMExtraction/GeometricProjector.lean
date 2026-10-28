import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingComparisonProjectors
import OAI.NumberTheory.PadicHodge.IntrinsicModel

/-! # Geometric Projector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricProjector.Intrinsic

noncomputable section

/-! The coefficient projectors retain their actual TateComparison action, full
characters, and the ranges of every coefficient conjugate. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

def GeometricProjectorIdentification
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure D.H1) (L : IntermediateField ℚ ℂ)
    (n : ℕ) (p : Fin n → L ⊗[ℚ] (D.H1 →ₗ[ℚ] D.H1)) : Prop :=
  ∃ (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (coeff : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ),
    AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D A coeff) ∧
    ∃ (j : AlgebraicClosure ℚ →+* ℂ) (hLalg : L ≤ HeckeCycles.Coefficients.CM.algebraicField)
      (χ : Fin n → AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] AlgebraicClosure ℚ),
      let P := fun k => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L D.H1 D.H1 (p k)
      let C := fun k => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L D.H1 D.H1 (p k))
      (∀ k, LinearMap.range (P k) = Definitions.CM.conjugateSpace L (C k) 1) ∧
      (∀ k h, Commute (P k) ((A.cohomologyAction h).baseChange ℂ)) ∧
      (∀ k, LinearMap.range (P k) = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace
        (fun h => (A.cohomologyAction h).baseChange ℂ) (fun h => j (χ k h))) ∧
      (∀ k (σ : Gal(L/ℚ)),
        let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L D.H1 D.H1
          (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ L (D.H1 →ₗ[ℚ] D.H1) σ (p k))
        ∃ τ : Gal(AlgebraicClosure ℚ/ℚ),
          (∀ a : L, j (τ ((HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm
            (IntermediateField.inclusion hLalg a))) = (σ a : ℂ)) ∧
          Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H ∧
          LinearMap.range Pσ = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace
            (fun h => (A.cohomologyAction h).baseChange ℂ) (fun h => j (τ (χ k h))))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricProjector.Intrinsic
