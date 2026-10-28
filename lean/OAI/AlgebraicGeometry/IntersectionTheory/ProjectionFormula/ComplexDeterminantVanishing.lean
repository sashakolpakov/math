import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.InjectiveDeterminant
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalDivisibility
import Mathlib.RingTheory.Flat.Basic

/-! # Complex Determinant Vanishing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantVanishing

noncomputable section

/-! A three-term free complex over a normal Noetherian domain which is
exact at all height-one primes has associated numerator and denominator
determinants. Its generically exact restriction to a PID has Euler
characteristic zero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.Module _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

local instance : DecidableEq (ι ⊕ κ) := Classical.decEq _

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantBaseChange

theorem associated_determinants (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (hf : Function.Injective f) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t))
    (a : Basis ι R A) (b : Basis (ι ⊕ κ) R B) (c : Basis κ R C)
    (hex : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      (ComplexDeterminantBaseChange.complex R (Localization.AtPrime p) f g h).ShortExact) :
    Associated (LinearMap.toMatrix (a.prod c) b (f.coprod t)).det (g.comp t).det := by
  apply NormalDivisibility.associated_of_orders R
  · exact InjectiveDeterminant.matrix_ne_zero R (a.prod c) b _
      (ShortComplexDeterminant.coprod_injective R f g h hf t ht)
  · exact InjectiveDeterminant.end_ne_zero R c _ ht
  · intro p hprime hp
    let S := Localization.AtPrime p
    let : IsDiscreteValuationRing S := NormalDivisibility.localization_dvr R p hp
    have hS := hex p hp
    have hfS : Function.Injective (f.baseChange S) := hS.moduleCat_injective_f
    have htS : Function.Injective ((g.comp t).baseChange S) :=
      Module.Flat.lTensor_preserves_injective_linearMap (g.comp t) ht
    have hr : (g.baseChange S).range = ⊤ :=
      LinearMap.range_eq_top.mpr hS.moduleCat_surjective_g
    have h₀ : Module.length S ((S ⊗[R] C) ⧸ (g.baseChange S).range) = 0 := by
      rw [hr]
      exact Module.length_eq_zero
    have hz : IsZero (ComplexDeterminantBaseChange.complex R S f g h).homology :=
      (ComplexDeterminantBaseChange.complex R S f g h).exact_iff_isZero_homology.mp hS.exact
    let : Subsingleton (ComplexDeterminantBaseChange.complex R S f g h).homology := ModuleCat.subsingleton_of_isZero hz
    have he := ComplexDeterminantBaseChange.order_comparison R S f g h t hfS htS a b c
    rw [h₀, Module.length_eq_zero, add_zero, zero_add] at he
    exact he

theorem euler_zero (S : Type u) [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
    [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (hf : Function.Injective f) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t))
    (a : Basis ι R A) (b : Basis (ι ⊕ κ) R B) (c : Basis κ R C)
    (hex : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      (ComplexDeterminantBaseChange.complex R (Localization.AtPrime p) f g h).ShortExact)
    (hfS : Function.Injective (f.baseChange S))
    (htS : Function.Injective ((g.comp t).baseChange S)) :
    ((Module.length S ((S ⊗[R] C) ⧸ (g.baseChange S).range)).toNat : ℚ) -
        ((Module.length S (ComplexDeterminantBaseChange.complex R S f g h).homology).toNat : ℚ) = 0 := by
  rw [ComplexDeterminantBaseChange.euler_eq R S f g h t hfS htS a b c]
  have he := (associated_determinants R f g h hf t ht a b c hex).map (algebraMap R S)
  rw [Ring.ord_eq_of_associated he, sub_self]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantVanishing
