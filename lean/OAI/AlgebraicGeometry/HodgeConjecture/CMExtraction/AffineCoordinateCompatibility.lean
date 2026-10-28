import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic

/-! # Affine Coordinate Compatibility -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineCoordinateCompatibility.TestTransport

noncomputable section

/-! Linear coordinate comparisons are preserved by the divided
differences defining the original principal congruence subgroup. -/

open scoped Classical

theorem linear_pair_smul_sub {R V W Z : Type*} [CommRing R]
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
    [Module R V] [Module R W] [Module R Z]
    (f : V →ₗ[R] Z) (g : W →ₗ[R] Z) (r : R)
    (a b : V) (x y : W) (ha : f a = g x) (hb : f b = g y) :
    f (r • (a - b)) = g (r • (x - y)) := by
  simp only [map_smul, map_sub, ha, hb]

variable (E : Type) [Field E] [NumberField E]
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (e : (I → E) ≃ₗ[ℚ] (J → ℚ))

def completedPadicCoordinate (p : ℕ) [Fact p.Prime] (j : J) :
    (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) →ₗ[ℚ] Padic p :=
  (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toLinearMap.comp
    (((LinearMap.proj j).comp (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).toLinearMap).restrictScalars ℚ)

def rationalPadicCoordinate (p : ℕ) [Fact p.Prime] (j : J) : (I → E) →ₗ[ℚ] Padic p :=
  (Algebra.linearMap ℚ (Padic p)).comp ((LinearMap.proj j).comp e.toLinearMap)

theorem coordinate_smul_sub_compatibility (p : ℕ) [Fact p.Prime] (j : J)
    (r : ℚ) (Y Z : I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) (x y : I → E)
    (hY : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j) =
      algebraMap ℚ (Padic p) (e x j))
    (hZ : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Z j) =
      algebraMap ℚ (Padic p) (e y j)) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (r • (Y - Z)) j) =
      algebraMap ℚ (Padic p) (e (r • (x - y)) j) :=
  linear_pair_smul_sub (completedPadicCoordinate E e p j) (rationalPadicCoordinate E e p j)
    r Y Z x y hY hZ

theorem completedPadicCoordinate_rational (p : ℕ) [Fact p.Prime] (j : J) (x : I → E) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
      (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (x i)) j) = algebraMap ℚ (Padic p) (e x j) := by
  have h := congrArg (fun z : J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (z j))
    (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational E e x)
  exact h.trans ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).commutes _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineCoordinateCompatibility.TestTransport
