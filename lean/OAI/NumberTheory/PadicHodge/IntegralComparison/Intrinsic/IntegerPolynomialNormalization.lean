import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleIntegerCharacteristicPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.DegreePolynomialPlusNormalization

/-! # Integer Polynomial Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.IntegerPolynomialNormalization.Geometric.AbelianModel

noncomputable section

/-! The integer polynomial of the original model has its actual geometric
degree normalization on every finite dominant positive Frobenius shift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

attribute [local instance] GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_group GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_commutative
  GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_proper GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_smooth GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_integral

local instance : IsIntegral A.geometricSpecialFiber.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.geometricSpecialFiber.hom

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial_eval_neg_nat (n : ℕ)
    [IsFinite ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) + A.nativeGeometricFrobenius).toMul.hom.hom.left]
    [IsDominant ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) + A.nativeGeometricFrobenius).toMul.hom.hom.left] :
    A.nativeIntegerFrobeniusPolynomial.eval (-(n : ℤ)) =
      (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) + A.nativeGeometricFrobenius).toMul.hom.hom.left.residueDegree
        (genericPoint A.geometricSpecialFiber.left) : ℤ) :=
  DegreePolynomialPlusNormalization.GeometricResultant.integerPolynomial_eval_neg_nat
    A.geometricSpecialFiber A.nativeGeometricFrobenius n

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial_degree_twice_dimension :
    A.nativeIntegerFrobeniusPolynomial.natDegree =
      2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.geometricSpecialFiber.hom :=
  Geometric.DegreeResultant.integerPolynomial_natDegree
    A.geometricSpecialFiber A.nativeGeometricFrobenius

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.IntegerPolynomialNormalization.Geometric.AbelianModel
