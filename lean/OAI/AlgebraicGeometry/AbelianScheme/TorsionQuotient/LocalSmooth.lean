import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero
import Mathlib.RingTheory.Smooth.Basic

/-! # Local Smooth -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalSmooth.LocalSmoothCriterion

/-!
# TorsionQuotient: local square-zero extensions detect formal smoothness of local rings

The universal first-order thickening of a polynomial presentation is local
when its quotient is local. A section of this actual thickening proves
formal smoothness by the standard presentation criterion.
-/

universe u

theorem isLocalHom_of_surjective_squareZero
    {C B : Type u} [CommRing C] [CommRing B] (p : C →+* B)
    (hp : Function.Surjective p) (hker : RingHom.ker p ^ 2 = ⊥) : IsLocalHom p where
  map_nonunit a ha := by
    obtain ⟨r, hr⟩ := ha
    obtain ⟨b, hb⟩ := hp (↑r⁻¹ : B)
    have he : a * b - 1 ∈ RingHom.ker p := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, ← hr, hb, Units.mul_inv, sub_self]
    have hn : IsNilpotent (a * b - 1) :=
      ⟨2, by simpa only [pow_two] using
        InfinitesimalEq.Infinitesimal.mul_eq_zero_of_square_zero_ideal (RingHom.ker p) hker he he⟩
    have hu : IsUnit (a * b) := by
      simpa only [sub_add_cancel] using hn.isUnit_add_right_of_commute isUnit_one (Commute.all ..)
    exact isUnit_of_mul_isUnit_left hu

theorem domain_isLocalRing_of_squareZero
    {C B : Type u} [CommRing C] [CommRing B] [IsLocalRing B] (p : C →+* B)
    (hp : Function.Surjective p) (hker : RingHom.ker p ^ 2 = ⊥) : IsLocalRing C := by
  let : IsLocalHom p := isLocalHom_of_surjective_squareZero p hp hker
  exact p.domain_isLocalRing

/-- To prove a local algebra formally smooth it suffices to split all
surjective square-zero extensions by local algebras. -/
theorem formallySmooth_of_local_sections
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (H : ∀ (C : Type u) [CommRing C] [Algebra R C] [IsLocalRing C]
      (p : C →ₐ[R] A), Function.Surjective p → RingHom.ker p.toRingHom ^ 2 = ⊥ →
      ∃ g : A →ₐ[R] C, p.comp g = AlgHom.id R A) : Algebra.FormallySmooth R A := by
  let P := Algebra.Generators.self R A
  let f := IsScalarTower.toAlgHom R P.Ring A
  rw [Algebra.FormallySmooth.iff_split_surjection f P.algebraMap_surjective]
  have hp : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ P.algebraMap_surjective
  have hker : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let : IsLocalRing (P.Ring ⧸ RingHom.ker f.toRingHom ^ 2) :=
    domain_isLocalRing_of_squareZero f.kerSquareLift.toRingHom hp hker
  exact H _ f.kerSquareLift hp hker

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalSmooth.LocalSmoothCriterion
