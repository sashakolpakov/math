import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.SwitchOf
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Background

/-! # Rational Hodge -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalHodge.CM.Abelian

/-!
CMAbelianVariety's final application, with every input explicit.

SurfaceConstruction now supplies the switch premise via a constructed fourfold product.
DegreeTwo supplies fullness and geometric degree-two algebraicity; ExteriorCohomology supplies
exterior cohomology. These are exact bridges to committed specifications.

This reusable application keeps the generic Riemann realization and
cycle-to-Hodge inclusion as explicit parameters. `RiemannRealization`
and `CycleClasses` prove them from the geometric background;
`CMAbelianVarietyFinal` supplies those proofs and exposes only exact graph statements.
The original statement in Statements/CMAbelianVariety.lean is unchanged.
-/

/-- The exact proposition of the committed CMReduction specification. -/
def SwitchReductionInput : Prop :=
  (∀ (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E],
    ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E) →
  ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic →
  ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne →
  ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology →
  ComplexMultiplication.CMKnownResults.CM.KnownResults.CycleClassesAreHodge →
  (∀ (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E],
    CMReduction.Definitions.CM.FourFactorSwitchAlgebraicity E) →
  ComplexMultiplication.CMCore.CM.cmHodgeClaim

/-- The unchanged CMAbelianVariety conclusion after the explicitly listed background inputs. -/
theorem rational_hodge_conjecture_for_cm_abelian_varieties_of_inputs
    (hCMReduction : SwitchReductionInput)
    (hSurfaceConstruction : SwitchOf.CM.Abelian.SwitchCycleInput)
    (hDegreeTwo_weight_one : Background.CM.Abelian.WeightOneAlgebraicityInput)
    (hDegreeTwo_degree_two : Background.CM.Abelian.DegreeTwoAlgebraicityInput)
    (hExteriorCohomology : Background.CM.Abelian.ExteriorCohomologyInput)
    (hRiemann : ∀ (E : IntermediateField ℚ ℂ)
      [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E],
      ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (hCycleClasses : ComplexMultiplication.CMKnownResults.CM.KnownResults.CycleClassesAreHodge)
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.variety.rationalCohomology 1))
    (h_holomorphic : H.holomorphic = X.h1Holomorphic)
    (h_antiholomorphic : H.antiholomorphic = X.h1Antiholomorphic)
    (decomposition : ComplexMultiplication.Decomposition.CM.CMDecomposition H)
    (p : ℕ)
    (hp : p ≤ X.variety.complexDimension) :
    LinearMap.range (X.variety.geometricCycleClassMap p) =
      X.variety.rationalHodgeClasses p := by
  have hCM : X.HasCMH1 :=
    ⟨H, h_holomorphic, h_antiholomorphic, ⟨decomposition⟩⟩
  exact hCMReduction hRiemann
    (Background.CM.Abelian.rationalH1MapsAreAlgebraic_of_DegreeTwo hDegreeTwo_weight_one)
    (Background.CM.Abelian.lefschetzOneOne_of_DegreeTwo hDegreeTwo_degree_two)
    (Background.CM.Abelian.abelianExteriorCohomology_of_ExteriorCohomology hExteriorCohomology)
    hCycleClasses (SwitchOf.CM.Abelian.fourFactorSwitchAlgebraicity_of_SurfaceConstruction hSurfaceConstruction)
    X hCM p hp

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalHodge.CM.Abelian
