import OAI.AlgebraicGeometry.HodgeConjecture.GeometricDescent
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Products

/-! # Geometric Four -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.GeometricFour.LefschetzNormalization.Geometry

noncomputable section

/-! The actual twofold/fourfold products, their embedding tensor comparison
maps, and scalar conjugation of the resulting geometric classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

def cup22Coefficient (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (E ⊗[ℚ] X.rationalCohomology 2) →ₗ[E]
      (E ⊗[ℚ] X.rationalCohomology 2) →ₗ[E] (E ⊗[ℚ] X.rationalCohomology 4) :=
  LinearMap.BilinMap.baseChange E
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 2 2)

theorem cup22Coefficient_conjugate (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (g : Gal(E/ℚ))
    (x y : E ⊗[ℚ] X.rationalCohomology 2) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 4) g (cup22Coefficient E X x y) =
      cup22Coefficient E X (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 2) g x)
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 2) g y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp [hx, hz]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul b y => simp [cup22Coefficient, LinearMap.BilinMap.baseChange_tmul]

theorem cup22Coefficient_realize (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x y : E ⊗[ℚ] X.rationalCohomology 2) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 4 (cup22Coefficient E X x y) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 2 2
        (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 2 x) (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 2 y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp [hx, hz]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul b y =>
      simp only [cup22Coefficient, LinearMap.BilinMap.baseChange_tmul,
        Coefficients.CM.SurfaceConstruction.realizeCoefficient_tmul, IntermediateField.coe_mul]
      change ((a : ℂ) * (b : ℂ)) •
        AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) 4
          (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 2 2 x y) = _
      erw [map_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul, mul_comm (b : ℂ) (a : ℂ)]
      exact congrArg (fun z => ((a : ℂ) * (b : ℂ)) • z)
        (ComplexMultiplication.HodgeComparison.RationalCup.CM.Construction.rationalToComplexCohomology_cup (Betti.Scheme.schemePointSpace X.toOver) 2 2 x y)

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

def lineComparison {v : LefschetzNormalization.Sign E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : X.toOver ⟶ R.abelianVariety.toOver) :
    ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] X.complexCohomology 1 :=
  (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 π).hom.comp R.complexComparison.toLinearMap

/-- This is the canonical cup of projection pullbacks on the actual tensor
product of the two complexified rational CM spaces. -/
def pairTensorComparison {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) :
    ComplexMultiplication.WeightOne.CM.Complexification E ⊗[ℂ] ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] X.complexCohomology 2 :=
  TensorProduct.lift
    (((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1).compl₂
      (lineComparison E T X πT)).comp (lineComparison E R X πR))

theorem pairTensorComparison_embedding {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E) :
    pairTensorComparison E R T X πR πT
        (LefschetzNormalization.embeddingGenerator E a ⊗ₜ[ℂ] LefschetzNormalization.embeddingGenerator E b) =
      GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E R T X πR πT a b := rfl

def fourClass {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) :
    X.complexCohomology 4 :=
  AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 2 2
    (GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E (R 0) (R 1) X (π 0) (π 1) (a 0) (a 1))
    (GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E (R 2) (R 3) X (π 2) (π 3) (a 2) (a 3))

def fourCoefficient {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) :
    E ⊗[ℚ] X.rationalCohomology 4 :=
  cup22Coefficient E X
    (GeometricCoefficients.LefschetzNormalization.Geometry.pairCoefficient E (R 0) (R 1) X (π 0) (π 1) (a 0) (a 1))
    (GeometricCoefficients.LefschetzNormalization.Geometry.pairCoefficient E (R 2) (R 3) X (π 2) (π 3) (a 2) (a 3))

theorem fourCoefficient_realize {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 4 (fourCoefficient E R X π a) = fourClass E R X π a := by
  rw [fourCoefficient, cup22Coefficient_realize, GeometricCoefficients.LefschetzNormalization.Geometry.pairCoefficient_realize,
    GeometricCoefficients.LefschetzNormalization.Geometry.pairCoefficient_realize]
  rfl

theorem fourCoefficient_conjugate {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) (g : LefschetzNormalization.G E) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 4) g (fourCoefficient E R X π a) =
      fourCoefficient E R X π (fun i => g * a i) := by
  rw [fourCoefficient, cup22Coefficient_conjugate, GeometricCoefficients.LefschetzNormalization.Geometry.pairCoefficient_conjugate,
    GeometricCoefficients.LefschetzNormalization.Geometry.pairCoefficient_conjugate]
  rfl

abbrev FourTensor :=
  (ComplexMultiplication.WeightOne.CM.Complexification E ⊗[ℂ] ComplexMultiplication.WeightOne.CM.Complexification E) ⊗[ℂ]
    (ComplexMultiplication.WeightOne.CM.Complexification E ⊗[ℂ] ComplexMultiplication.WeightOne.CM.Complexification E)

def fourTensorComparison {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) :
    FourTensor E →ₗ[ℂ] X.complexCohomology 4 :=
  TensorProduct.lift
    (((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 2 2).compl₂
      (pairTensorComparison E (R 2) (R 3) X (π 2) (π 3))).comp
      (pairTensorComparison E (R 0) (R 1) X (π 0) (π 1)))

def embeddingTensor (a : Fin 4 → LefschetzNormalization.G E) : FourTensor E :=
  (LefschetzNormalization.embeddingGenerator E (a 0) ⊗ₜ[ℂ] LefschetzNormalization.embeddingGenerator E (a 1)) ⊗ₜ[ℂ]
    (LefschetzNormalization.embeddingGenerator E (a 2) ⊗ₜ[ℂ] LefschetzNormalization.embeddingGenerator E (a 3))

theorem fourTensorComparison_embedding {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) :
    fourTensorComparison E R X π (embeddingTensor E a) = fourClass E R X π a := rfl

theorem fourClass_scalar_iff {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) (g : LefschetzNormalization.G E) :
    fourClass E R X π (fun i => g * a i) ∈ X.complexGeometricAlgebraicClasses 2 ↔
      fourClass E R X π a ∈ X.complexGeometricAlgebraicClasses 2 := by
  rw [← fourCoefficient_realize, ← fourCoefficient_realize,
    ← fourCoefficient_conjugate, GeometricDescent.LefschetzNormalization.Geometry.complex_geometric_scalarConjugate_iff]

/-- Markings of actual CM realizations, as geometric data rather than
properties of unknown cycle classes. -/
abbrev RealizationFamily := ∀ v : LefschetzNormalization.Sign E, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)

def A₂ (R : RealizationFamily E) (u v : LefschetzNormalization.Sign E) (a b : LefschetzNormalization.G E) : Prop :=
  let X := Albanese.Construction.SegreClosed.abelianProduct (R u).abelianVariety (R v).abelianVariety
  GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E (R u) (R v) X.variety (CartesianMonoidalCategory.fst _ _)
    (CartesianMonoidalCategory.snd _ _) a b ∈ X.variety.complexGeometricAlgebraicClasses 1

def A₄ (R : RealizationFamily E) (v : LefschetzNormalization.FourTypes E) (a : Fin 4 → LefschetzNormalization.G E) : Prop :=
  let X := CMVariety.Products.CM.Abelian.fourProduct (fun i => (R (v i)).abelianVariety)
  fourClass E (fun i => R (v i)) X.variety (CMVariety.Products.CM.Abelian.fourProjection _) a ∈
    X.variety.complexGeometricAlgebraicClasses 2

theorem A₂_of_balance (R : RealizationFamily E)
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (u v : LefschetzNormalization.Sign E) (a b : LefschetzNormalization.G E)
    (h : ∀ g : LefschetzNormalization.G E, ComplexMultiplication.SignSwitch.CM.signValue (u.val (g * a)) + ComplexMultiplication.SignSwitch.CM.signValue (v.val (g * b)) = 0) :
    A₂ E R u v a b :=
  GeometricCoefficients.LefschetzNormalization.Geometry.pairClass_algebraic E hScalarDescent hDegreeTwo (R u) (R v) _ _ _ a b h

theorem A₄_scalar_iff (R : RealizationFamily E)
    (v : LefschetzNormalization.FourTypes E) (a : Fin 4 → LefschetzNormalization.G E) (g : LefschetzNormalization.G E) :
    A₄ E R v (fun i => g * a i) ↔ A₄ E R v a :=
  fourClass_scalar_iff E _ _ _ a g

end

end OAI.AlgebraicGeometry.HodgeConjecture.GeometricFour.LefschetzNormalization.Geometry
