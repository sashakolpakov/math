import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntrinsicHecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingComparisonProjectors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction

/-! # Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Projectors.CM.Hecke

noncomputable section

/-! Construct algebraic Hodge projectors for the actual source GeometricTheta
theta classes and the same full Hecke action, retaining commutation,
all occurring characters, and every coefficient-conjugate range. -/

open scoped Classical TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntrinsicHecke.Intrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness D hg hq hIsogenyQuotient)
  (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) (j : AlgebraicClosure ℚ →+* ℂ)

def Output : Prop :=
  ∃ F : IntermediateField ℚ ℂ, NumberField F ∧ IsGalois ℚ F ∧ E ≤ F ∧
    ∃ (hFalg : F ≤ Coefficients.CM.algebraicField) (n : ℕ)
      (p : Fin n → F ⊗[ℚ] (D.pel.H1 →ₗ[ℚ] D.pel.H1))
      (χ : Fin n → AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] AlgebraicClosure ℚ),
      let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F D.pel.H1 D.pel.H1 (p i)
      let A := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange F D.pel.H1 D.pel.H1 (p i))
      let H := CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg
      let θ := Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W
      (∀ i, (P i).comp (P i) = P i) ∧
      (∀ i, LinearMap.range (P i) = CMExtraction.Definitions.CM.conjugateSpace F (A i) 1) ∧
      (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) ∧
      (∀ i h, Commute (P i) ((W.action.cohomologyAction h).baseChange ℂ)) ∧
      (∀ i, ∃ φ, P i (θ φ) ≠ 0) ∧
      (∀ φ, ∑ i, P i (θ φ) = θ φ) ∧
      (∀ i, LinearMap.range (P i) = HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
        (fun h => j (χ i h))) ∧
      (∀ i (σ : Gal(F/ℚ)),
        let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F D.pel.H1 D.pel.H1
          (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F (D.pel.H1 →ₗ[ℚ] D.pel.H1) σ (p i))
        ∃ τ : Gal(AlgebraicClosure ℚ/ℚ),
          (∀ a : F, j (τ ((ChosenCharacters.CM.chosenClosureEquiv j).symm
            (IntermediateField.inclusion hFalg a))) = (σ a : ℂ)) ∧
          Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H ∧
          LinearMap.range Pσ = HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
            (fun h => j (τ (χ i h))))

theorem exists_projectors
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) : Output E D hg hq hIsogenyQuotient W hHodgeDecomposition j := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
  exact CMExtraction.CommutingComparisonProjectors.Spectral.construct_commuting_comparison_projectors E (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg)
    W.action.cohomologyAction
    (CMExtraction.IntrinsicHecke.Intrinsic.native_hecke_isHodgeMap D hHodgeDecomposition hConstruction hHodgeComparison hg hq hIsogenyQuotient W.action W.realization)
    (Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W) j

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Projectors.CM.Hecke
