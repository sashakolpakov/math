import OAI.AlgebraicGeometry.Divisors.LineBundles.TwoEquationSymmetry
import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationFiniteLength
import Mathlib.RingTheory.Ideal.Operations

/-! # Local Intersection Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite local intersection lengths for two equations

The actual double cokernel is R/(a,b), and all kernel/cokernel lengths
are finite when this quotient has finite length. For two nonzero
equations in a domain, the intersection Euler length is symmetric.
When the second multiplication on the quotient is injective, the
correction kernel vanishes and the invariant is the usual quotient length.
-/

variable {R : Type*} [CommRing R] (a b : R)

theorem equationEndomorphism_range_eq_span : (MultiplicationSequence.BundleCycles.equationEndomorphism a R).range = Ideal.span {a} :=
  Ideal.range_mul' a

def twoEquationCokernelIdealEquiv :
    MultiplicationSequence.BundleCycles.equationCokernel a (MultiplicationSequence.BundleCycles.equationCokernel b R) ≃ₗ[R] R ⧸ Ideal.span {a, b} := by
  have h : (MultiplicationSequence.BundleCycles.equationEndomorphism b R).range ⊔ (MultiplicationSequence.BundleCycles.equationEndomorphism a R).range = Ideal.span {a, b} := by
    rw [equationEndomorphism_range_eq_span, equationEndomorphism_range_eq_span, sup_comm]
    exact (Ideal.span_insert a {b}).symm
  exact (TwoEquationSymmetry.BundleCycles.twoEquationCokernelQuotientEquiv a b).trans (Submodule.quotEquivOfEq _ _ h)

theorem equationCokernel_annihilated (M : Type*) [AddCommGroup M] [Module R M] :
    Module.IsTorsionBy R (MultiplicationSequence.BundleCycles.equationCokernel a M) a := by
  apply (Module.isTorsionBy_quotient_iff (MultiplicationSequence.BundleCycles.equationEndomorphism a M).range a).mpr
  intro x
  exact ⟨x, rfl⟩

variable [IsNoetherianRing R]

/-- The finite local intersection invariant of the two actual equations. -/
def localIntersectionLength (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b})) : ℤ :=
  EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI (equationCokernel_annihilated b R)

omit [IsNoetherianRing R] in
theorem twoEquationQuotientFinite_swap (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b})) :
    IsFiniteLength R (R ⧸ Ideal.span {b, a}) :=
  (congrArg (fun I : Ideal R => IsFiniteLength R (R ⧸ I)) (Ideal.span_pair_comm (x := a) (y := b))).mp hI

/-- Symmetry follows from the two actual kernel and cokernel identifications. -/
theorem localIntersectionLength_comm [IsDomain R] (ha : a ≠ 0) (hb : b ≠ 0)
    (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b})) :
    localIntersectionLength a b hI = localIntersectionLength b a (twoEquationQuotientFinite_swap a b hI) :=
  TwoEquationSymmetry.BundleCycles.equationEulerLength_comm a b (TwoEquationSymmetry.BundleCycles.equationEndomorphism_injective a ha) (TwoEquationSymmetry.BundleCycles.equationEndomorphism_injective b hb)
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations a b hI (equationCokernel_annihilated b R))
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations a b hI (equationCokernel_annihilated b R))
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations b a (twoEquationQuotientFinite_swap a b hI) (equationCokernel_annihilated a R))
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations b a (twoEquationQuotientFinite_swap a b hI) (equationCokernel_annihilated a R))

/-- For a regular multiplication on R/bR, the invariant is the actual length of R/(a,b). -/
theorem localIntersectionLength_eq_quotientLength
    (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b}))
    (ha : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism a (MultiplicationSequence.BundleCycles.equationCokernel b R))) :
    localIntersectionLength a b hI = ((Module.length R (R ⧸ Ideal.span {a, b})).toNat : ℤ) := by
  have hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a (MultiplicationSequence.BundleCycles.equationCokernel b R)) = 0 := by
    change Module.length R (MultiplicationSequence.BundleCycles.equationEndomorphism a (MultiplicationSequence.BundleCycles.equationCokernel b R)).ker = 0
    rw [LinearMap.ker_eq_bot.mpr ha, Module.length_bot]
  unfold localIntersectionLength EquationFiniteLength.BundleCycles.twoEquationEulerLength EquationEulerLength.BundleCycles.equationEulerLength
  rw [hK, ENat.toNat_zero, Nat.cast_zero, sub_zero, (twoEquationCokernelIdealEquiv a b).length_eq]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionLength.BundleCycles
