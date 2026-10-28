import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Finite Order Localization Lift -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteOrderLocalizationLift

noncomputable section

/-! Localization into a noncommutative algebra is possible through the
commutative image when the localized generator has finite order. -/

abbrev algHomRangeCommRing {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Ring B] [Algebra R B] (f : A →ₐ[R] B) : CommRing f.range where
  toRing := inferInstance
  mul_comm := by
    intro x y
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    apply Subtype.ext
    change x.val * y.val = y.val * x.val
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm a b]

theorem exists_algHom_of_finiteOrder_localization
    {R A L B : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing L] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
    [Ring B] [Algebra R B] (z : A) [IsLocalization.Away z L]
    (f : A →ₐ[R] B) (n : ℕ) (hn : n ≠ 0) (hp : f z ^ n = 1) :
    ∃ g : L →ₐ[R] B, ∀ a : A, g (algebraMap A L a) = f a := by
  let : CommRing f.range := algHomRangeCommRing f
  let f' : A →ₐ[R] f.range := f.rangeRestrict
  have he : f' z ^ n = 1 := Subtype.ext hp
  have hu : IsUnit (f' z) := IsUnit.of_pow_eq_one he hn
  let g : L →ₐ[R] f.range := IsLocalization.Away.liftAlgHom z hu
  refine ⟨f.range.val.comp g, ?_⟩
  intro a
  exact congrArg Subtype.val (IsLocalization.Away.lift_eq (S := L) z hu a)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteOrderLocalizationLift
