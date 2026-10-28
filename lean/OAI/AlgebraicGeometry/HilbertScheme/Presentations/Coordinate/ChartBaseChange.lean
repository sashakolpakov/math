import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorPolynomialEquiv
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorLocalizedDegrees
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.ModuleEquivalences
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientChartDegrees

/-! # Chart Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.ChartBaseChange.GradedHilbert

noncomputable section

/-! Explicit base-change equivalences for actual homogeneous coordinate-quotient charts, in every integer degree. -/

open _root_.MvPolynomial TensorProduct DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientChartDegrees.ProjectiveCech

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateModuleChartBaseChangeEquiv (s : Finset (Fin (n + 1))) :
    S ⊗[R] Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s ≃ₗ[R]
      Graded.ModuleRestriction.ProjectiveCech.ModuleChart S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal) s :=
  (TensorProduct.comm R S (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s)).trans
    ((TensorModuleLocalization.GradedModules.awayModuleTensorEquiv R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) S (LaurentMonomials.ProjectiveCech.inversionMonomial R s)).trans
      ((Localized.ModuleEquivalences.GradedModules.awayModuleLinearEquiv (R := R) (Quotient.TensorPolynomialEquiv.GradedHilbert.quotientTensorPolynomialEquiv (S := S) I) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)).trans
        (CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal) s)))

theorem coordinateModuleChartBaseChangeEquiv_fraction (s : Finset (Fin (n + 1))) (r : S) (k : ℕ)
    (m : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) :
    coordinateModuleChartBaseChangeEquiv (S := S) I s
      (r ⊗ₜ[R] Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k m) =
        Module.Fractions.GradedModules.moduleFractionMap (R := S) (LaurentMonomials.ProjectiveCech.inversionMonomial S s) k (Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I (r ⊗ₜ[R] m)) := by
  simp only [coordinateModuleChartBaseChangeEquiv, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorModuleLocalization.GradedModules.awayModuleTensorEquiv_fraction, Localized.ModuleEquivalences.GradedModules.awayModuleLinearEquiv_fraction, CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv_fraction,
    Quotient.TensorPolynomialEquiv.GradedHilbert.quotientTensorPolynomialEquiv_tmul]

def coordinateModuleChartDegreeBaseChangeEquiv (s : Finset (Fin (n + 1))) (d : ℤ) :
    S ⊗[R] Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) s d ≃ₗ[R]
      Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
        (IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) s d := by
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I
  let ℳ := IntegerQuotient.GradedHilbert.integerQuotientGrading I
  let 𝒩 := IntegerQuotient.GradedHilbert.integerQuotientGrading J
  let := tensorDecomposition ℳ S
  let := TensorGradedAction.GradedModules.decomposeTensor_gradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) R) ℳ S
  let := Graded.ScalarRestriction.GradedModules.restrictScalarsDecomposition (R := R) 𝒩
  let := Graded.ScalarRestriction.GradedModules.coefficientRestriction_gradedSMul (σ := Fin (n + 1)) (R := R) 𝒩
  let e₁ := TensorLocalizedDegrees.GradedModules.tensorLocalizedDegreeEquiv (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) R) ℳ S
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) d
  let e₂ := Localized.ModuleEquivalences.GradedModules.localizedDegreeLinearEquiv (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) R) (decomposeTensor ℳ S)
    (fun j => (𝒩 j).restrictScalars R) (Quotient.TensorPolynomialEquiv.GradedHilbert.quotientTensorPolynomialEquiv (S := S) I)
    (Quotient.TensorPolynomialEquiv.GradedHilbert.quotientTensorPolynomialEquiv_homogeneous I) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)
    (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) d
  let e₃ := CoefficientChartDegrees.ProjectiveCech.coefficientModuleChartDegreeEquiv R S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ J.toIdeal) 𝒩 s d
  exact (TensorProduct.comm R S (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) ℳ s d)).trans
    (e₁.trans (e₂.trans e₃))

theorem coordinateModuleChartDegreeBaseChangeEquiv_val (s : Finset (Fin (n + 1))) (d : ℤ)
    (x : S ⊗[R] Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) s d) :
    (coordinateModuleChartDegreeBaseChangeEquiv (S := S) I s d x).val =
      coordinateModuleChartBaseChangeEquiv (S := S) I s
        (((Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (IntegerQuotient.GradedHilbert.integerQuotientGrading I) s d).subtype.lTensor S) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m => rfl
  | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, Submodule.coe_add, hx, hy]

theorem coordinateModuleChartBaseChangeEquiv_restriction {s t : Finset (Fin (n + 1))} (h : s ⊆ t)
    (x : S ⊗[R] Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s) :
    coordinateModuleChartBaseChangeEquiv (S := S) I t
      ((Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h).lTensor S x) =
        Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal) h
          (coordinateModuleChartBaseChangeEquiv (S := S) I s x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    obtain ⟨k, z, rfl⟩ := Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) m
    simp only [LinearMap.lTensor_tmul, Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_fraction,
      coordinateModuleChartBaseChangeEquiv_fraction]
    apply congrArg (Module.Fractions.GradedModules.moduleFractionMap (R := S) (LaurentMonomials.ProjectiveCech.inversionMonomial S t) k)
    rw [← Quotient.TensorPolynomialEquiv.GradedHilbert.quotientTensorPolynomialEquiv_tmul, ← Quotient.TensorPolynomialEquiv.GradedHilbert.quotientTensorPolynomialEquiv_tmul]
    change Quotient.TensorPolynomialEquiv.GradedHilbert.quotientTensorPolynomialEquiv (S := S) I
      ((LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k) • (z ⊗ₜ[R] r)) = _
    rw [map_smul, ← CoefficientModuleCharts.ProjectiveCech.inversionMonomial_coefficientMap R S (t \ s), ← map_pow]
    exact (IsScalarTower.algebraMap_smul (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k) _).symm
  | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.ChartBaseChange.GradedHilbert
