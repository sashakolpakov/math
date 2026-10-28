import OAI.AlgebraicGeometry.HodgeConjecture.LefschetzNormalization
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CoefficientVectors
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.OppositePairs

/-! # Geometric Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.GeometricCoefficients.LefschetzNormalization.Geometry

noncomputable section

/-!
# Concrete embedding classes for LefschetzNormalization

All coefficients below belong to the rational singular cohomology of the
specified actual variety. Algebraicity means membership in the image of its
geometric cycle-class map after extending scalars to the given CM field.
The two realized factors and their markings are independent. No algebraicity
predicate, tensor comparison, or conjugation law is assumed.
-/

open _root_.CategoryTheory
open scoped TensorProduct Classical

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

/-- The specified CM line transported by its actual rational marking and
an algebraic map to the variety on which the cup product is taken. -/
def pulledCoefficient {v : LefschetzNormalization.Sign E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : X.toOver ⟶ R.abelianVariety.toOver)
    (a : LefschetzNormalization.G E) : E ⊗[ℚ] X.rationalCohomology 1 :=
  (((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 π).hom.comp
    R.comparison.toLinearMap).baseChange E) (CMReduction.CoefficientVectors.CM.Construction.coefficientVector E a)

def pulledClass {v : LefschetzNormalization.Sign E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : X.toOver ⟶ R.abelianVariety.toOver)
    (a : LefschetzNormalization.G E) : X.complexCohomology 1 :=
  Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 π
    (R.complexComparison (LefschetzNormalization.embeddingGenerator E a))

theorem pulledCoefficient_realize {v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : X.toOver ⟶ R.abelianVariety.toOver)
    (a : LefschetzNormalization.G E) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 1 (pulledCoefficient E R X π a) = pulledClass E R X π a := by
  unfold Coefficients.CM.SurfaceConstruction.realizeCoefficient pulledCoefficient
  rw [ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_baseChange, CMReduction.CoefficientVectors.CM.Construction.coefficientVector_inclusion,
    LinearMap.baseChange_comp, LinearMap.comp_apply, Pairs.CM.SurfaceConstruction.complexification_pullback]
  rfl

theorem pulledCoefficient_conjugate {v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : X.toOver ⟶ R.abelianVariety.toOver)
    (g a : LefschetzNormalization.G E) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 1) g (pulledCoefficient E R X π a) =
      pulledCoefficient E R X π (g * a) := by
  unfold pulledCoefficient
  rw [ComplexMultiplication.EmbeddingCoefficientField.CM.scalarConjugate_baseChange, CMReduction.CoefficientVectors.CM.Construction.coefficientVector_conjugate]

def pairCoefficient {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E) :
    E ⊗[ℚ] X.rationalCohomology 2 :=
  Pairs.CM.SurfaceConstruction.coefficientH1Cup E X (pulledCoefficient E R X πR a) (pulledCoefficient E T X πT b)

def pairClass {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E) :
    X.complexCohomology 2 :=
  AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace X.toOver) 1 1
    (pulledClass E R X πR a) (pulledClass E T X πT b)

theorem pairCoefficient_realize {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 2 (pairCoefficient E R T X πR πT a b) =
      pairClass E R T X πR πT a b := by
  rw [pairCoefficient, Pairs.CM.SurfaceConstruction.realizeCoefficient_h1Cup, pulledCoefficient_realize,
    pulledCoefficient_realize]
  rfl

theorem pairCoefficient_conjugate {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (g a b : LefschetzNormalization.G E) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 2) g
      (pairCoefficient E R T X πR πT a b) =
      pairCoefficient E R T X πR πT (g * a) (g * b) := by
  rw [pairCoefficient, Pairs.CM.SurfaceConstruction.coefficientH1Cup_conjugate, pulledCoefficient_conjugate,
    pulledCoefficient_conjugate]
  rfl

theorem pulledClass_holomorphic {v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : X.toOver ⟶ R.abelianVariety.toOver)
    (a : LefschetzNormalization.G E) (ha : v.val a = true) :
    pulledClass E R X π a ∈ X.pureBettiSubspace 1 0 := by
  apply Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace π 1 0
  apply (R.complexComparison_holomorphic _).mpr
  exact (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_holomorphic E v a).mpr ha

theorem pulledClass_antiholomorphic {v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : X.toOver ⟶ R.abelianVariety.toOver)
    (a : LefschetzNormalization.G E) (ha : v.val a = false) :
    pulledClass E R X π a ∈ X.pureBettiSubspace 0 1 := by
  apply Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace π 0 1
  apply (R.complexComparison_antiholomorphic _).mpr
  exact (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_antiholomorphic E v a).mpr ha

theorem pairClass_hodge {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E)
    (h : ComplexMultiplication.SignSwitch.CM.signValue (u.val a) + ComplexMultiplication.SignSwitch.CM.signValue (v.val b) = 0) :
    pairClass E R T X πR πT a b ∈ X.pureBettiSubspace 1 1 := by
  have ho := (LefschetzNormalization.sign_pair_zero_iff _ _).mp h
  by_cases hu : u.val a = true
  · have hv : v.val b = false := by simpa only [hu, Bool.not_true] using ho
    exact AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveCup_mem_pure X 1 0 0 1 _ _
      (pulledClass_holomorphic E R X πR a hu)
      (pulledClass_antiholomorphic E T X πT b hv)
  · have hu' : u.val a = false := Bool.eq_false_iff.mpr hu
    have hv : v.val b = true := by simpa only [hu', Bool.not_false] using ho
    exact AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveCup_mem_pure X 0 1 1 0 _ _
      (pulledClass_antiholomorphic E R X πR a hu')
      (pulledClass_holomorphic E T X πT b hv)

/-- Full orbitwise sign cancellation produces an actual divisor class over E.
This invokes the specified scalar-descent and degree-two propositions. -/
theorem pairCoefficient_algebraic
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    {u v : LefschetzNormalization.Sign E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E)
    (h : ∀ g : LefschetzNormalization.G E, ComplexMultiplication.SignSwitch.CM.signValue (u.val (g * a)) + ComplexMultiplication.SignSwitch.CM.signValue (v.val (g * b)) = 0) :
    pairCoefficient E R T X πR πT a b ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 1 := by
  apply Coefficients.CM.SurfaceConstruction.degreeTwo_algebraic_of_conjugates E hScalarDescent hDegreeTwo
  intro g
  rw [pairCoefficient_conjugate, pairCoefficient_realize]
  exact pairClass_hodge E R T X πR πT (g * a) (g * b) (h g)

theorem pairClass_algebraic
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    {u v : LefschetzNormalization.Sign E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E)
    (h : ∀ g : LefschetzNormalization.G E, ComplexMultiplication.SignSwitch.CM.signValue (u.val (g * a)) + ComplexMultiplication.SignSwitch.CM.signValue (v.val (g * b)) = 0) :
    pairClass E R T X πR πT a b ∈ X.complexGeometricAlgebraicClasses 1 := by
  rw [← pairCoefficient_realize]
  exact CMReduction.OppositePairs.CM.Construction.coefficient_algebraic_realize E X 1
    (pairCoefficient_algebraic E hScalarDescent hDegreeTwo R T X πR πT a b h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.GeometricCoefficients.LefschetzNormalization.Geometry
