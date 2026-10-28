import OAI.ArithmeticGeometry.Models.SpreadingOut.Fg
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # Base -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Base.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

abbrev fieldBase (K : Type u) [Field K] : Scheme.{u} :=
  Spec (CommRingCat.of K)

/-- The arithmetic-base definition from the SpreadingOut specification, with
noncomputability made explicit by the enclosing section. -/
structure ArithmeticOpen (K : Type u) [Field K] [NumberField K] where
  U : (Spec (CommRingCat.of (NumberField.RingOfIntegers K))).Opens
  finite_complement :
    ((U : Set (Spec
      (CommRingCat.of (NumberField.RingOfIntegers K))))ᶜ).Finite
  generic : fieldBase K ⟶ U.toScheme
  generic_eq :
    generic ≫ U.ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (NumberField.RingOfIntegers K) K))

abbrev integerBasicOpen (K : Type u) [Field K]
    (d : NumberField.RingOfIntegers K) :
    (Spec (CommRingCat.of (NumberField.RingOfIntegers K))).Opens :=
  PrimeSpectrum.basicOpen d

/-- The generic point factors through every nonzero principal open. -/
theorem generic_range_subset_basicOpen
    (K : Type u) [Field K] [NumberField K]
    (d : NumberField.RingOfIntegers K) (hd : d ≠ 0) :
    Set.range
      (Spec.map (CommRingCat.ofHom
        (algebraMap (NumberField.RingOfIntegers K) K))) ⊆
      (integerBasicOpen K d : Set
        (Spec (CommRingCat.of (NumberField.RingOfIntegers K)))) := by
  rintro _ ⟨p, rfl⟩
  let q : PrimeSpectrum K := p
  change algebraMap (NumberField.RingOfIntegers K) K d ∉ q.asIdeal
  rw [Ideal.eq_bot_of_prime (I := q.asIdeal), Ideal.mem_bot]
  exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hd

/-- Inverting a nonzero algebraic integer gives an arithmetic base of
the precise kind required by the SpreadingOut statement. -/
def arithmeticOpenOfNonzero
    (K : Type u) [Field K] [NumberField K]
    (d : NumberField.RingOfIntegers K) (hd : d ≠ 0) : ArithmeticOpen K where
  U := integerBasicOpen K d
  finite_complement := Fg.Construction.finite_complement_basicOpen d hd
  generic := IsOpenImmersion.lift (integerBasicOpen K d).ι
    (Spec.map (CommRingCat.ofHom (algebraMap (NumberField.RingOfIntegers K) K)))
    (by simpa using generic_range_subset_basicOpen K d hd)
  generic_eq := IsOpenImmersion.lift_fac _ _ _

/-- Finite disjoint open components with geometrically connected fibers,
using the same condition as the statement specification. -/
def HasSplitGeometricComponents {S : Scheme.{u}} (X : Over S) : Prop :=
  ∃ (n : ℕ) (C : Fin n → X.left.Opens),
    (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
    (⨆ i, C i) = ⊤ ∧
    ∀ i, GeometricallyConnected ((C i).ι ≫ X.hom)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Base.Construction
