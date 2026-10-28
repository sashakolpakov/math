import Mathlib

/-! # Basis Rational -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BasisRational.Construction

noncomputable section

/-! An integral basis of a full lattice is a basis of its rational span. -/

open scoped Classical
open _root_.Module

theorem integralBasis_coe_span
    {L ι : Type*} [AddCommGroup L] (Λ : Submodule ℤ L) (b : Basis ι ℤ Λ) :
    Submodule.span ℤ (Set.range (fun i => (b i).val)) = Λ := by
  have he : (Submodule.span ℤ (Set.range b)).map Λ.subtype = Λ := by
    rw [b.span_eq, Submodule.map_top, Submodule.range_subtype]
  rw [Submodule.map_span, ← Set.range_comp] at he
  exact he

def rationalBasisOfIntegralBasis
    {L ι : Type*} [AddCommGroup L] [Module ℚ L]
    (Λ : Submodule ℤ L) (hΛ : Submodule.span ℚ (Λ : Set L) = ⊤) (b : Basis ι ℤ Λ) :
    Basis ι ℚ L := by
  have hlin : LinearIndependent ℚ (fun i => (b i).val) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (b.linearIndependent.map' Λ.subtype Λ.ker_subtype)
  apply Basis.mk hlin
  have he := congrArg (fun M : Submodule ℤ L => Submodule.span ℚ (M : Set L))
    (integralBasis_coe_span Λ b)
  rw [Submodule.span_span_of_tower, hΛ] at he
  exact he.ge

theorem rationalBasisOfIntegralBasis_apply
    {L ι : Type*} [AddCommGroup L] [Module ℚ L]
    (Λ : Submodule ℤ L) (hΛ : Submodule.span ℚ (Λ : Set L) = ⊤) (b : Basis ι ℤ Λ) (i : ι) :
    rationalBasisOfIntegralBasis Λ hΛ b i = (b i).val := by
  simp [rationalBasisOfIntegralBasis]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BasisRational.Construction
