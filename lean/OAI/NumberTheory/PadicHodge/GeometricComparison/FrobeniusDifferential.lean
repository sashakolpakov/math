import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms

/-! # Frobenius Differential -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusDifferential.FrobeniusDifferentialDivisibility

noncomputable section

/-! A lift of the prime-power map modulo the prime has prime-divisible pullback on actual Kähler one-forms. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

universe u

variable {R : Type u} [CommRing R] (p : ℕ) (A : CommAlgCat.{u} R) (f : A ⟶ A)

theorem on_derivation (h : ∀ a : A, ∃ b : A, f a = a ^ p + (p : A) * b) (a : A) :
    ∃ ω : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.OneForms R A, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap f (KaehlerDifferential.D R A a) = p • ω := by
  obtain ⟨b, hb⟩ := h a
  refine ⟨a ^ (p - 1) • KaehlerDifferential.D R A a + KaehlerDifferential.D R A b, ?_⟩
  rw [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_D, hb, map_add, Derivation.leibniz_pow, Derivation.leibniz,
    Derivation.map_natCast, smul_zero, add_zero, Nat.cast_smul_eq_nsmul, nsmul_add]

theorem on_oneForms (h : ∀ a : A, ∃ b : A, f a = a ^ p + (p : A) * b)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.OneForms R A) : ∃ η : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.OneForms R A, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap f ω = p • η := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact on_derivation p A f h a
  | zero => exact ⟨0, by rw [map_zero, nsmul_zero]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, by rw [map_add, ha, hb, nsmul_add]⟩
  | smul a x hx ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨f a • b, by rw [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_smul, hb, smul_comm]⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusDifferential.FrobeniusDifferentialDivisibility
