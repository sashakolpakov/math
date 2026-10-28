import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Flat -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Flat

noncomputable section

/-! Flat modules have no higher local Tor, and degree-zero Tor is the
ordinary tensor product. These are comparisons for the exact categorical
Tor functor used by ThomClass's intersection multiplicity. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)

def torZeroIso : ((Tor (ModuleCat R) 0).obj M).obj N ≅ ModuleCat.of R (M ⊗[R] N) :=
  ((tensorLeft M).leftDerivedZeroIsoSelf).app N

theorem torZero_length : Module.length R (((Tor (ModuleCat R) 0).obj M).obj N) =
    Module.length R (M ⊗[R] N) := by
  exact (torZeroIso R M N).toLinearEquiv.length_eq

theorem higherTor_isZero [Module.Flat R M] (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj N) := by
  let P := projectiveResolution N
  apply IsZero.of_iso _ (P.isoLeftDerivedObj (tensorLeft M) (n + 1))
  change IsZero ((((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact (P.exact_succ n).map (tensorLeft M)

theorem higherTor_length [Module.Flat R M] (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) (n + 1)).obj M).obj N) = 0 := by
  let := ModuleCat.subsingleton_of_isZero (higherTor_isZero R M N n)
  exact Module.length_eq_zero

theorem torZero_length_of_unit (e : M ≃ₗ[R] R) :
    Module.length R (((Tor (ModuleCat R) 0).obj M).obj N) = Module.length R N := by
  rw [torZero_length]
  exact ((TensorProduct.congr e (LinearEquiv.refl R N)).trans
    (TensorProduct.lid R N)).length_eq

theorem euler_length_of_flat [Module.Flat R M] (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj M).obj N)).toNat) =
      (Module.length R (M ⊗[R] N)).toNat := by
  rw [Finset.sum_range_succ']
  simp [higherTor_length, torZero_length]

theorem euler_length_of_unit (e : M ≃ₗ[R] R) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj M).obj N)).toNat) =
      (Module.length R N).toNat := by
  let : Module.Flat R M := Module.Flat.of_linearEquiv e
  rw [Finset.sum_range_succ']
  simp [higherTor_length, torZero_length_of_unit R M N e]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Flat
