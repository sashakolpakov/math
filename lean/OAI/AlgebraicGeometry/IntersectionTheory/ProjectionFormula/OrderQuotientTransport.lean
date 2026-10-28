import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Divisor
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Order Quotient Transport -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport

noncomputable section

section

/-! Local orders are invariant under compatible isomorphisms of the local
rings and their actual fraction fields. This connects affine localization
calculations with scheme stalks without replacing the divisor definition. -/

theorem ord_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let eA : R ≃ₐ[R] S := { e with commutes' := fun _ => rfl }
  have hI : Ideal.span {e a} = (Ideal.span {a}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eQ := Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) eA hI
  exact (Module.length_eq_of_surjective (R := S) (M := S ⧸ Ideal.span {e a})
    e.surjective).symm.trans eQ.toLinearEquiv.length_eq.symm

theorem ordMonoid_equiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    (e : R ≃+* S) (a : R) :
    Ring.ordMonoidWithZeroHom S (e a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · subst a
    simp only [map_zero]
  have ha' : e a ≠ 0 := (map_ne_zero_iff _ e.injective).mpr ha
  have hR : Ring.ord R a = ((Ring.ord R a).toNat : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm
  have hS := (ord_equiv e a).trans hR
  rw [Ring.ordMonoidWithZeroHom_eq_coe S (mem_nonZeroDivisors_of_ne_zero ha') hS,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero ha) hR]

/-- Compatibility with the structure maps fixes the fraction-field order
under the given ring and field isomorphisms. -/
theorem ordFrac_equiv {R S K L : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (e : R ≃+* S) (φ : K ≃+* L)
    (hφ : ∀ a : R, φ (algebraMap R K a) = algebraMap S L (e a)) (f : K) :
    Ring.ordFrac S (φ f) = Ring.ordFrac R f := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [map_div₀, hφ a, hφ b, map_div₀, map_div₀,
    Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb',
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ e.injective).mpr ha),
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ e.injective).mpr hb'),
    ordMonoid_equiv e a, ordMonoid_equiv e b]

end

section

/-! Orders in a surjective ring target equal the orders in its actual
kernel quotient, with the specified element retained. -/

theorem ord {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (r : R) :
    Ring.ord S (f r) = Ring.ord (R ⧸ RingHom.ker f) (Ideal.Quotient.mk _ r) := by
  have h := ord_equiv (RingHom.quotientKerEquivOfSurjective (f := f) hf)
    (Ideal.Quotient.mk _ r)
  simpa only [RingHom.quotientKerEquivOfSurjective_apply_mk] using h

end

/-! Principal colengths on quotient rings are preserved by the
actual ambient ring isomorphism and its transported defining ideal. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Ring

theorem equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : J = I.map e.toRingHom) (r : R) :
    Ring.ord (S ⧸ J) (Ideal.Quotient.mk J (e r)) =
      Ring.ord (R ⧸ I) (Ideal.Quotient.mk I r) := by
  exact (congrArg (Ring.ord (S ⧸ J)) (Ideal.quotientEquiv_mk I J e h r)).symm.trans
    (ord_equiv (Ideal.quotientEquiv I J e h) (Ideal.Quotient.mk I r))

end Ring

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport
