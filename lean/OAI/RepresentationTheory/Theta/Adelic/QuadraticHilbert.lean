import OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization

/-! # Quadratic Hilbert -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticHilbert

noncomputable section

/-! An explicit Hilbert 90 calculation for the global quadratic field.
It will identify the scalar idele-class image by a closed rationality
condition on the conjugation quotient. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization.Construction

theorem quadratic_hilbert90
    {F : Type*} [Field F] [CharZero F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ) (hu : u * star u = 1) :
    ∃ b : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ, b / star b = u := by
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := ⟨by
    intro r hr
    apply hns
    exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩⟩
  by_cases hneg : u = -1
  · refine ⟨Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd, ?_⟩
    rw [hneg, div_eq_iff_eq_mul]
    apply Units.ext
    apply QuadraticAlgebra.ext <;> simp [Weil.AdelicSplitting.Normalization.Construction.deltaUnit]
  · have hb : (1 : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) + u.val ≠ 0 := by
      intro h
      apply hneg
      apply Units.ext
      change u.val = -(1 : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)
      exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
    refine ⟨Units.mk0 (1 + u.val) hb, ?_⟩
    rw [div_eq_iff_eq_mul]
    apply Units.ext
    change 1 + u.val = u.val * star (1 + u.val)
    rw [star_add, star_one, mul_add, mul_one]
    have h := congrArg Units.val hu
    change u.val * star u.val = 1 at h
    rw [h, add_comm]

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticHilbert
