import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Symmetric Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart.BundleCycles

noncomputable section

/-! The distinguished affine chart of Proj Sym(R ⊕ M), with its actual
dehomogenization map to Sym(M). -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def augmentedSymmetricVariable : SymmetricAlgebra R (R × M) :=
  SymmetricAlgebra.ι R (R × M) (1, 0)

theorem augmentedSymmetricVariable_degree :
    augmentedSymmetricVariable R M ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 1 := by
  change SymmetricAlgebra.ι R (R × M) (1, 0) ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R (R × M)) (1, 0)

def symmetricDehomogenizingLinear : R × M →ₗ[R] SymmetricAlgebra R M :=
  (Algebra.linearMap R (SymmetricAlgebra R M)).comp (LinearMap.fst R R M) +
    (SymmetricAlgebra.ι R M).comp (LinearMap.snd R R M)

def symmetricDehomogenizingMap : SymmetricAlgebra R (R × M) →ₐ[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift (symmetricDehomogenizingLinear R M)

theorem symmetricDehomogenizingMap_generator (r : R) (m : M) :
    symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) (r, m)) =
      algebraMap R (SymmetricAlgebra R M) r + SymmetricAlgebra.ι R M m :=
  SymmetricAlgebra.lift_ι_apply (symmetricDehomogenizingLinear R M) (r, m)

theorem symmetricDehomogenizingMap_variable :
    symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M) = 1 := by
  change symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) (1, 0)) = 1
  rw [symmetricDehomogenizingMap_generator, map_one, map_zero, add_zero]

abbrev augmentedSymmetricChart : Type :=
  Away (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (augmentedSymmetricVariable R M)

def augmentedSymmetricDehomogenization : augmentedSymmetricChart R M →+* SymmetricAlgebra R M :=
  (Localization.awayLift (symmetricDehomogenizingMap R M).toRingHom (augmentedSymmetricVariable R M)
    (by change IsUnit (symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M));
        rw [symmetricDehomogenizingMap_variable]; exact isUnit_one)).comp
    (algebraMap (augmentedSymmetricChart R M) (Localization.Away (augmentedSymmetricVariable R M)))

theorem augmentedSymmetricDehomogenization_mk (n : ℕ) (a : SymmetricAlgebra R (R × M))
    (ha : a ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (n • 1)) :
    augmentedSymmetricDehomogenization R M
      (Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (augmentedSymmetricVariable_degree R M) n a ha) =
        symmetricDehomogenizingMap R M a := by
  have hu : IsUnit ((symmetricDehomogenizingMap R M).toRingHom (augmentedSymmetricVariable R M)) := by
    change IsUnit (symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M))
    rw [symmetricDehomogenizingMap_variable]
    exact isUnit_one
  change Localization.awayLift (symmetricDehomogenizingMap R M).toRingHom (augmentedSymmetricVariable R M) hu
    (Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (augmentedSymmetricVariable_degree R M) n a ha).val = _
  rw [Away.val_mk]
  have h := Localization.awayLift_mk (symmetricDehomogenizingMap R M).toRingHom
    (augmentedSymmetricVariable R M) a 1 (by
      change symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M) * 1 = 1
      rw [symmetricDehomogenizingMap_variable, mul_one]) n
  exact h.trans (by rw [one_pow, mul_one]; rfl)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart.BundleCycles
