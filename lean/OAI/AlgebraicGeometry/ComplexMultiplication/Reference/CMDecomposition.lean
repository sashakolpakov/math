import OAI.AlgebraicGeometry.ComplexMultiplication.FieldProductComponents
import OAI.AlgebraicGeometry.ComplexMultiplication.CoordinateSum
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalHodgeMaps
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Endomorphisms

/-! # CM Decomposition -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-! # The original CM input supplies the canonical geometric CM decomposition -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {n : ℕ} (K : Fin n → Type) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
  [∀ i, NumberField.IsCMField (K i)] (e : U ≃ₗ[ℚ] ((i : Fin n) → K i))
  (H : WeightOne.CM.WeightOneHodgeStructure U) (h : ∀ a, WeightOne.CM.IsHodgeMap H H (Definitions.diagonalAction K e a))

/-- Coordinatewise multiplication gives the original finite internal CM direct sum. -/
def Reference.CMDecomposition.cmProductDecomposition : Decomposition.CM.CMDecomposition H where
  numberOfComponents := n
  component := FieldProductComponents.cmProductComponent K e H h
  isInternal := CoordinateSum.cmCoordinateSubspaces_internal K e

omit [∀ i, NumberField.IsCMField (K i)] in
theorem Reference.CMDecomposition.diagonalAction_intertwines {W : Type*} [AddCommGroup W] [Module ℚ W]
    (b : W ≃ₗ[ℚ] U) (a : (i : Fin n) → K i) :
    b.toLinearMap.comp (Definitions.diagonalAction K (b.trans e) a) =
      (Definitions.diagonalAction K e a).comp b.toLinearMap := by
  ext u
  apply e.injective
  have hn := DiagonalAction.model_diagonalAction K (b.trans e) a u
  have ho := DiagonalAction.model_diagonalAction K e a (b u)
  exact (show e (b (Definitions.diagonalAction K (b.trans e) a u)) = a * e (b u) from hn).trans ho.symm

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

/-- The actual rational Betti bridge transports the original rank-one field model. -/
def Definitions.CMH1Data.nativeModel (d : Definitions.CMH1Data X) :
    Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1 ≃ₗ[ℚ]
      ((i : Fin d.factors) → d.field i) :=
  (Reference.BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).trans d.model

/-- The transported action retains the originally supplied holomorphic filtration. -/
theorem Definitions.CMH1Data.nativeModel_hodge (d : Definitions.CMH1Data X) (a : (i : Fin d.factors) → d.field i) :
    WeightOne.CM.IsHodgeMap (CanonicalAbelianWeightOne.originalCanonicalH1 X) (CanonicalAbelianWeightOne.originalCanonicalH1 X)
      (Definitions.diagonalAction d.field (d.nativeModel X) a) := by
  apply Reference.CanonicalHodgeMaps.h1HodgeMap_of_intertwines X (Definitions.diagonalAction d.field d.model a) _
    (Hodge.Endomorphisms.diagonalAction_mem_h1HodgeEndomorphismAlgebra X d a)
  exact Reference.CMDecomposition.diagonalAction_intertwines d.field d.model
    (Reference.BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1) a

/-- No cycle-class premise is added when converting the original CM hypothesis. -/
def Definitions.CMH1Data.canonicalDecomposition (d : Definitions.CMH1Data X) : Decomposition.CM.CMDecomposition (CanonicalAbelianWeightOne.originalCanonicalH1 X) :=
  Reference.CMDecomposition.cmProductDecomposition d.field (d.nativeModel X) (CanonicalAbelianWeightOne.originalCanonicalH1 X)
    (d.nativeModel_hodge X)

/-- The challenge's exact CM assumption supplies the older geometric theorem's CM input. -/
theorem Reference.CMDecomposition.originalCMInput_hasCMH1 (hCM : Definitions.HasComplexMultiplication X) :
    (BundledAbelianBridge.originalAbelianVariety X).HasCMH1 := by
  obtain ⟨d⟩ := hCM
  exact ⟨CanonicalAbelianWeightOne.originalCanonicalH1 X, rfl, rfl, ⟨d.canonicalDecomposition X⟩⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication
