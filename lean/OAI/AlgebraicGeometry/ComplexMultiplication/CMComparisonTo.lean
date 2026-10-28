import OAI.AlgebraicGeometry.ComplexMultiplication.Definitions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # CM Comparison To -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMComparisonTo

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-!
# Coefficient maps for the CM comparison

Rational coefficients are a direct summand of complex coefficients as rational
vector spaces. The resulting retraction on constant sheaf complexes proves
injectivity of the rational-to-de Rham comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped TensorProduct

variable (X : Over (Spec ↧ℂ))

/-- Put a constant additive coefficient sheaf in degree zero. -/
def coefficientComplexFunctor :
    AddCommGrpCat ⥤ CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X) ⋙
    CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)

/-- A rational-linear retraction of the canonical coefficient inclusion. -/
def rationalCoefficientRetraction : ℂ →ₗ[ℚ] ℚ :=
  (Algebra.linearMap ℚ ℂ).leftInverse

theorem rationalCoefficientRetraction_algebraMap (q : ℚ) :
    rationalCoefficientRetraction (algebraMap ℚ ℂ q) = q := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (RingHom.injective (algebraMap ℚ ℂ))) q

/-- Retraction from the complex constant sheaf complex to the rational one. -/
def rationalCoefficientComplexRetraction :
    ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℂ X ⟶ ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X :=
  (coefficientComplexFunctor X).map
    (AddCommGrpCat.ofHom rationalCoefficientRetraction.toAddMonoidHom)

theorem rationalCoefficientComplex_leftInverse :
    ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X ≫
      rationalCoefficientComplexRetraction X = 𝟙 _ := by
  change (coefficientComplexFunctor X).map
      (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
    (coefficientComplexFunctor X).map
      (AddCommGrpCat.ofHom rationalCoefficientRetraction.toAddMonoidHom) = 𝟙 _
  rw [← Functor.map_comp]
  have h : AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom ≫
      AddCommGrpCat.ofHom rationalCoefficientRetraction.toAddMonoidHom = 𝟙 _ := by
    ext q
    exact rationalCoefficientRetraction_algebraMap q
  rw [h]
  exact CategoryTheory.Functor.map_id _ _

theorem hypercohomologyMap_id_apply
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (z : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (𝟙 K) n z = z := by
  exact Localization.SmallShiftedHom.comp_mk₀_id _ _ _

theorem rationalToComplexHypercohomology_injective (n : ℤ) :
    Function.Injective
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n) := by
  apply Function.LeftInverse.injective
    (g := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (rationalCoefficientComplexRetraction X) n)
  intro z
  rw [← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    rationalCoefficientComplex_leftInverse, hypercohomologyMap_id_apply]

/-- An arbitrary rational coordinate functional on the complex coefficients. -/
def coefficientFunctionalComplex (r : ℂ →ₗ[ℚ] ℚ) :
    ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℂ X ⟶ ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X :=
  (coefficientComplexFunctor X).map (AddCommGrpCat.ofHom r.toAddMonoidHom)

theorem coefficientFunctionalComplex_scalar (r : ℂ →ₗ[ℚ] ℚ) (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X ≫
      ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c ≫ coefficientFunctionalComplex X r =
    ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex ℚ X (r c) := by
  change (coefficientComplexFunctor X).map
      (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
    (coefficientComplexFunctor X).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft c)) ≫
    (coefficientComplexFunctor X).map (AddCommGrpCat.ofHom r.toAddMonoidHom) =
    (coefficientComplexFunctor X).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (r c)))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  ext q
  change r (c * algebraMap ℚ ℂ q) = r c * q
  calc
    r (c * algebraMap ℚ ℂ q) = r (q • c) := by
      congr 1
      simp [Algebra.smul_def, mul_comm]
    _ = q • r c := r.map_smul q c
    _ = r c * q := by simp [smul_eq_mul, mul_comm]

variable [IsIntegral X.left] [Smooth X.hom]

/-- The canonical rational-to-de Rham comparison has no rational kernel. -/
theorem rationalToDeRham_injective (n : ℕ) :
    Function.Injective (ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n) := by
  have hC : Function.Injective
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)) :=
    (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamEquiv X (n : ℤ)).injective
  intro a b hab
  apply (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm.injective
  apply rationalToComplexHypercohomology_injective X (n : ℤ)
  apply hC
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt ℚ X) (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm a) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt ℚ X) (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm b) at hab
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X ≫
        ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm a) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X ≫
        ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm b) at hab
  simpa only [ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply] using hab

/-- Scalar extension on a pure tensor is the geometric comparison times its scalar. -/
theorem h1Comparison_tmul (c : ℂ) (v : H^1(X; ℚ)) :
    Definitions.h1Comparison X (c ⊗ₜ[ℚ] v) =
      c • ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X 1 v := by
  simp [Definitions.h1Comparison, Algebra.lsmul_apply]

theorem h1Comparison_complex_smul (c : ℂ) (z : ℂ ⊗[ℚ] H^1(X; ℚ)) :
    Definitions.h1Comparison X (c • z) = c • Definitions.h1Comparison X z := by
  induction z using TensorProduct.inductionOn with
  | tmul d v =>
    change Definitions.h1Comparison X ((c * d) ⊗ₜ[ℚ] v) =
      c • Definitions.h1Comparison X (d ⊗ₜ[ℚ] v)
    rw [h1Comparison_tmul X, h1Comparison_tmul X, mul_smul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- The original scalar-extension comparison, with its complex linearity exposed. -/
def h1ComparisonComplex : ℂ ⊗[ℚ] H^1(X; ℚ) →ₗ[ℂ] H_dR^1(X) where
  toFun := Definitions.h1Comparison X
  map_add' := (Definitions.h1Comparison X).map_add
  map_smul' := h1Comparison_complex_smul X

theorem complexComparison_scalar (n : ℤ) (c : ℂ)
    (v : ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c) n v) =
      c • ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n v := by
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c) n v) =
    c • ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) n v
  rw [← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    ← ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt_scalar,
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ComplexPoint.Basic.ComplexSchemePoint.deRham_complex_smul_eq]

theorem complexComparison_symm_scalar (n : ℤ) (c : ℂ) (v : H_dR^n(X)) :
    (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).symm (c • v) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c) n
        ((ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).symm v) := by
  apply (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n).injective
  rw [AddEquiv.apply_symm_apply, complexComparison_scalar, AddEquiv.apply_symm_apply]

theorem complexComparison_symm_rational (n : ℕ) (v : H^n(X; ℚ)) :
    (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)).symm
        (ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n v) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) (n : ℤ)
        ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm v) := by
  apply (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)).injective
  rw [AddEquiv.apply_symm_apply]
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X ≫
        ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm v) = _
  exact ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X _ _ _ _

/-- Extract a rational coefficient after the genuine complex de Rham comparison. -/
def deRhamCoefficientFunctional (r : ℂ →ₗ[ℚ] ℚ) (n : ℕ) :
    H_dR^(n : ℤ)(X) →+ H^n(X; ℚ) :=
  (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).toAddMonoidHom.comp
    ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (coefficientFunctionalComplex X r) (n : ℤ)).comp
      (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)).symm.toAddMonoidHom)

theorem deRhamCoefficientFunctional_scalar_rational (r : ℂ →ₗ[ℚ] ℚ)
    (n : ℕ) (c : ℂ) (v : H^n(X; ℚ)) :
    deRhamCoefficientFunctional X r n
        (c • ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n v) = r c • v := by
  change (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n)
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (coefficientFunctionalComplex X r) (n : ℤ)
        ((ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)).symm
          (c • ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n v))) = r c • v
  rw [complexComparison_symm_scalar, complexComparison_symm_rational,
    ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    coefficientFunctionalComplex_scalar,
    ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_symm_smul, AddEquiv.apply_symm_apply]

/-- Contract the scalar factor of a tensor using a rational linear functional. -/
def tensorCoefficient (r : ℂ →ₗ[ℚ] ℚ) :
    ℂ ⊗[ℚ] H^1(X; ℚ) →ₗ[ℚ] H^1(X; ℚ) :=
  (TensorProduct.lid ℚ H^1(X; ℚ)).toLinearMap.comp (r.rTensor H^1(X; ℚ))

theorem deRhamCoefficientFunctional_h1Comparison (r : ℂ →ₗ[ℚ] ℚ)
    (z : ℂ ⊗[ℚ] H^1(X; ℚ)) :
    deRhamCoefficientFunctional X r 1 (Definitions.h1Comparison X z) = tensorCoefficient X r z := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    rw [h1Comparison_tmul, deRhamCoefficientFunctional_scalar_rational]
    simp [tensorCoefficient]
  | add x y hx hy => simp [hx, hy]

/-- The original scalar-extension map is injective, without a CM hypothesis. -/
theorem h1Comparison_injective : Function.Injective (Definitions.h1Comparison X) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker (Definitions.h1Comparison X)).eq_bot_iff.mpr
  intro z hz
  have hzero : Definitions.h1Comparison X z = 0 := hz
  have hc (r : ℂ →ₗ[ℚ] ℚ) : tensorCoefficient X r z = 0 := by
    rw [← deRhamCoefficientFunctional_h1Comparison, hzero, map_zero]
  let b := Module.Free.chooseBasis ℚ ℂ
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
  simpa [tensorCoefficient] using hc (b.coord i)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMComparisonTo
