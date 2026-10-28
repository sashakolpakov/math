import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial

/-! # Polynomial Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The polynomial determined by eventual finite-dimensional tensor-power section spaces is unique. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem Line.Bundles.LineBundle.sectionHilbertPolynomial_unique (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
    {P Q : Polynomial ℚ} (hP : L.HasSectionHilbertPolynomial p P) (hQ : L.HasSectionHilbertPolynomial p Q) : P = Q := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  let d₀ := max a b
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun m : ℕ => ((d₀ + m : ℕ) : ℚ)) := by
    intro m n h
    change ((d₀ + m : ℕ) : ℚ) = ((d₀ + n : ℕ) : ℚ) at h
    have he : d₀ + m = d₀ + n := by exact_mod_cast h
    exact Nat.add_left_cancel he
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro x ⟨m, rfl⟩
  exact (ha (d₀ + m) ((le_max_left a b).trans (Nat.le_add_right _ _))).2.trans
    (hb (d₀ + m) ((le_max_right a b).trans (Nat.le_add_right _ _))).2.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
