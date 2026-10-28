import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Polarization Multiple -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.PolarizationMultiple

noncomputable section

/-! The prescribed elementary divisors give an explicit multiple of
every integral functional in the image of the original polarization. -/

open scoped BigOperators

theorem zmod_product_annihilates {I : Type*} [Fintype I] (δ : I → ℕ)
    (a : ∀ i, ZMod (δ i)) : (∏ i, δ i) • a = 0 := by
  classical
  funext i
  change (∏ j, δ j) • a i = 0
  rw [nsmul_eq_mul]
  have hd : δ i ∣ ∏ j, δ j := Finset.dvd_prod_of_mem δ (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := hd
  rw [hm, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

omit [NumberField.IsCMField E] in
theorem referenceIntegralForm_multiple (hP : P.HasPolarizationType) (f : P.lattice →ₗ[ℤ] ℤ) :
    ∃ x : P.lattice, P.integralForm x = (∏ i, P.polarizationType i) • f := by
  obtain ⟨e⟩ := hP
  let c := Submodule.Quotient.mk (p := P.integralForm.range) f
  have hzero : (∏ i, P.polarizationType i) • c = 0 := by
    apply e.injective
    rw [map_nsmul, map_zero]
    apply Prod.ext
    · exact zmod_product_annihilates P.polarizationType (e c).1
    · exact zmod_product_annihilates P.polarizationType (e c).2
  have hm : (∏ i, P.polarizationType i) • f ∈ P.integralForm.range := by
    apply (Submodule.Quotient.mk_eq_zero P.integralForm.range).mp
    exact (map_nsmul (Submodule.mkQ P.integralForm.range) _ f).trans hzero
  exact hm

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.PolarizationMultiple
