import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Polynomials

/-! # Weighted Polynomials -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedPolynomials.GradedHilbert

noncomputable section

/-! Critical-pair homogeneity and degree control for arbitrary natural-number weights. -/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}
variable (w : Fin (n + 1) → ℕ) (m : MonomialOrder (Fin (n + 1)))

theorem naturalWeight_mono {a c : Fin (n + 1) →₀ ℕ} (hac : a ≤ c) :
    Finsupp.weight w a ≤ Finsupp.weight w c := by
  obtain ⟨b, rfl⟩ := le_iff_exists_add.mp hac
  rw [map_add]
  exact Nat.le_add_right _ _

theorem weighted_leadingDegree {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d : ℕ}
    (hf : f.IsWeightedHomogeneous w d) (hf0 : f ≠ 0) : Finsupp.weight w (m.degree f) = d :=
  hf (m.coeff_degree_ne_zero_iff.mpr hf0)

theorem sPolynomial_weighted_homogeneous {f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d e : ℕ}
    (hf : f.IsWeightedHomogeneous w d) (hg : g.IsWeightedHomogeneous w e) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    (m.sPolynomial f g).IsWeightedHomogeneous w (Finsupp.weight w (m.degree f ⊔ m.degree g)) := by
  have hdf := weighted_leadingDegree w m hf hf0
  have hdg := weighted_leadingDegree w m hg hg0
  have hleft : Finsupp.weight w (m.degree f ⊔ m.degree g - m.degree f) + d =
      Finsupp.weight w (m.degree f ⊔ m.degree g) := by
    rw [← hdf, ← map_add, tsub_add_cancel_of_le le_sup_left]
  have hright : Finsupp.weight w (m.degree f ⊔ m.degree g - m.degree g) + e =
      Finsupp.weight w (m.degree f ⊔ m.degree g) := by
    rw [← hdg, ← map_add, tsub_add_cancel_of_le le_sup_right]
  rw [MonomialOrder.sPolynomial_def]
  apply IsWeightedHomogeneous.sub
  · have h := (isWeightedHomogeneous_monomial w (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g)
      (rfl : Finsupp.weight w (m.degree f ⊔ m.degree g - m.degree f) = _)).mul hf
    simpa only [hleft] using h
  · have h := (isWeightedHomogeneous_monomial w (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff f)
      (rfl : Finsupp.weight w (m.degree f ⊔ m.degree g - m.degree g) = _)).mul hg
    simpa only [hright] using h

theorem sPolynomial_weighted_degree_bound {f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d e : ℕ}
    (hf : f.IsWeightedHomogeneous w d) (hg : g.IsWeightedHomogeneous w e) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    Finsupp.weight w (m.degree f ⊔ m.degree g) ≤ d + e := by
  rw [← weighted_leadingDegree w m hf hf0, ← weighted_leadingDegree w m hg hg0, ← map_add]
  exact naturalWeight_mono w (sup_le (le_add_right le_rfl) (le_add_left le_rfl))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedPolynomials.GradedHilbert
