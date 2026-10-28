import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Symmetric Polynomial -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricPolynomial.BundleCycles

noncomputable section

section

/-! The distinguished summand of an augmented symmetric algebra is
an actual polynomial variable over the module's symmetric algebra. -/

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def augmentedSymmetricPolynomialLinear : R × M →ₗ[R] Polynomial (SymmetricAlgebra R M) :=
  (LinearMap.fst R R M).smulRight Polynomial.X +
    ((Polynomial.CAlgHom (R := R) (A := SymmetricAlgebra R M)).toLinearMap.comp
      (SymmetricAlgebra.ι R M)).comp (LinearMap.snd R R M)

def augmentedSymmetricPolynomialMap : SymmetricAlgebra R (R × M) →ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  SymmetricAlgebra.lift (augmentedSymmetricPolynomialLinear R M)

theorem augmentedSymmetricPolynomialMap_generator (r : R) (m : M) :
    augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (r, m)) =
      r • Polynomial.X + Polynomial.C (SymmetricAlgebra.ι R M m) :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem augmentedSymmetricPolynomialMap_variable :
    augmentedSymmetricPolynomialMap R M (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) = Polynomial.X := by
  change augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (1, 0)) = _
  rw [augmentedSymmetricPolynomialMap_generator, one_smul, map_zero, map_zero, add_zero]

def augmentedSymmetricCoefficientMap : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (R × M) :=
  SymmetricAlgebra.lift (SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M)

theorem augmentedSymmetricCoefficientMap_generator (m : M) :
    augmentedSymmetricCoefficientMap R M (SymmetricAlgebra.ι R M m) =
      SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m := SymmetricAlgebra.lift_ι_apply _ _

def augmentedSymmetricPolynomialInverse : Polynomial (SymmetricAlgebra R M) →ₐ[R] SymmetricAlgebra R (R × M) :=
  Polynomial.eval₂AlgHom (augmentedSymmetricCoefficientMap R M) (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
    (fun _ => Commute.all _ _)

theorem augmentedSymmetricPolynomialInverse_C (a : SymmetricAlgebra R M) :
    augmentedSymmetricPolynomialInverse R M (Polynomial.C a) = augmentedSymmetricCoefficientMap R M a :=
  Polynomial.eval₂_C _ _

theorem augmentedSymmetricPolynomialInverse_X :
    augmentedSymmetricPolynomialInverse R M Polynomial.X = SymmetricChart.BundleCycles.augmentedSymmetricVariable R M :=
  Polynomial.eval₂_X _ _

end

/-! The actual polynomial decomposition of the augmented symmetric
algebra, including regularity of its distinguished coordinate. -/

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem augmentedSymmetricPolynomial_leftInverse :
    Function.LeftInverse (augmentedSymmetricPolynomialInverse R M) (augmentedSymmetricPolynomialMap R M) := by
  have h : (augmentedSymmetricPolynomialInverse R M).comp (augmentedSymmetricPolynomialMap R M) =
      AlgHom.id R (SymmetricAlgebra R (R × M)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    obtain ⟨r, m⟩ := v
    change augmentedSymmetricPolynomialInverse R M
      (augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (r, m))) =
        SymmetricAlgebra.ι R (R × M) (r, m)
    rw [augmentedSymmetricPolynomialMap_generator, map_add, map_smul,
      augmentedSymmetricPolynomialInverse_X, augmentedSymmetricPolynomialInverse_C,
      augmentedSymmetricCoefficientMap_generator]
    exact (SymmetricChartDegreeOne.BundleCycles.augmentedSymmetricGenerator_split R M r m).symm
  exact fun a => DFunLike.congr_fun h a

theorem augmentedSymmetricPolynomial_coefficient :
    (augmentedSymmetricPolynomialMap R M).comp (augmentedSymmetricCoefficientMap R M) =
      Polynomial.CAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro m
  change augmentedSymmetricPolynomialMap R M
    (augmentedSymmetricCoefficientMap R M (SymmetricAlgebra.ι R M m)) =
      Polynomial.C (SymmetricAlgebra.ι R M m)
  rw [augmentedSymmetricCoefficientMap_generator]
  change augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (0, m)) = _
  rw [augmentedSymmetricPolynomialMap_generator, zero_smul, zero_add]

theorem augmentedSymmetricPolynomial_rightInverse :
    Function.RightInverse (augmentedSymmetricPolynomialInverse R M) (augmentedSymmetricPolynomialMap R M) := by
  have h : (augmentedSymmetricPolynomialMap R M).comp (augmentedSymmetricPolynomialInverse R M) =
      AlgHom.id R (Polynomial (SymmetricAlgebra R M)) := by
    apply Polynomial.algHom_ext'
    · apply AlgHom.ext
      intro a
      change augmentedSymmetricPolynomialMap R M
        (augmentedSymmetricPolynomialInverse R M (Polynomial.C a)) = Polynomial.C a
      rw [augmentedSymmetricPolynomialInverse_C]
      exact DFunLike.congr_fun (augmentedSymmetricPolynomial_coefficient R M) a
    · change augmentedSymmetricPolynomialMap R M
        (augmentedSymmetricPolynomialInverse R M Polynomial.X) = Polynomial.X
      rw [augmentedSymmetricPolynomialInverse_X, augmentedSymmetricPolynomialMap_variable]
  exact fun a => DFunLike.congr_fun h a

def augmentedSymmetricPolynomialEquiv : SymmetricAlgebra R (R × M) ≃ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  { augmentedSymmetricPolynomialMap R M with
    invFun := augmentedSymmetricPolynomialInverse R M
    left_inv := augmentedSymmetricPolynomial_leftInverse R M
    right_inv := augmentedSymmetricPolynomial_rightInverse R M }

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricPolynomial.BundleCycles
