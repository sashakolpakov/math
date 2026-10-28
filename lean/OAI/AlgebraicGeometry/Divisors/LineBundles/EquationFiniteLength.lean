import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerLength
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Equation Finite Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EquationFiniteLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite local multiplication lengths for two equations

If R/(a,b) has finite length and a finite module is annihilated by b,
both the kernel and cokernel of multiplication by a have finite length.
Thus the intersection Euler length is defined from independent local
ring conditions, including in the presence of zero divisors.
-/

variable {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem moduleLength_ne_top_of_killedIdeal (I : Ideal R)
    (hI : IsFiniteLength R (R ⧸ I)) (hkill : Module.IsTorsionBySet R M I) : Module.length R M ≠ ⊤ := by
  let : Module (R ⧸ I) M := hkill.module
  let : IsScalarTower R (R ⧸ I) M := hkill.isScalarTower
  obtain ⟨_, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hI
  let : IsArtinian R (R ⧸ I) := hArt
  let : IsArtinianRing (R ⧸ I) := isArtinian_of_tower R inferInstance
  let : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
  let : IsNoetherian (R ⧸ I) M := isNoetherian_of_tower R inferInstance
  rw [Module.length_eq_of_surjective (R := R ⧸ I) (S := R) (M := M) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

theorem moduleLength_ne_top_of_two_annihilators (a b : R)
    (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b}))
    (ha : Module.IsTorsionBy R M a) (hb : Module.IsTorsionBy R M b) : Module.length R M ≠ ⊤ := by
  apply moduleLength_ne_top_of_killedIdeal (Ideal.span {a, b}) hI
  apply (Module.isTorsionBySet_iff_is_torsion_by_span ({a, b} : Set R)).mp
  intro x r
  rcases Set.mem_insert_iff.mp r.2 with h | h
  · change r.1 • x = 0
    rw [h]
    exact @ha x
  · change r.1 • x = 0
    rw [Set.mem_singleton_iff.mp h]
    exact @hb x

theorem equationKernel_finite_of_two_equations (a b : R)
    (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b})) (hb : Module.IsTorsionBy R M b) :
    Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M) ≠ ⊤ := by
  apply moduleLength_ne_top_of_two_annihilators a b hI
  · intro x
    exact Subtype.ext x.2
  · intro x
    exact Subtype.ext (@hb x.1)

theorem equationCokernel_finite_of_two_equations (a b : R)
    (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b})) (hb : Module.IsTorsionBy R M b) :
    Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M) ≠ ⊤ := by
  apply moduleLength_ne_top_of_two_annihilators a b hI
  · apply (Module.isTorsionBy_quotient_iff (MultiplicationSequence.BundleCycles.equationEndomorphism a M).range a).mpr
    intro x
    exact ⟨x, rfl⟩
  · exact hb.quotient (MultiplicationSequence.BundleCycles.equationEndomorphism a M).range

/-- The finite Euler length supplied by the actual two-equation local ring. -/
def twoEquationEulerLength (a b : R) (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b}))
    (hb : Module.IsTorsionBy R M b) : ℤ :=
  EquationEulerLength.BundleCycles.equationEulerLength a M (equationKernel_finite_of_two_equations a b hI hb)
    (equationCokernel_finite_of_two_equations a b hI hb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EquationFiniteLength.BundleCycles
