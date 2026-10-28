import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Finitely Generated Homogeneous Ideals -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FinitelyGeneratedHomogeneousIdeals.GradedHilbert

noncomputable section

/-! Finitely generated homogeneous ideals over arbitrary rings have a
finite generating set consisting of homogeneous elements. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem fg_homogeneous_generating_finset (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hfg : I.toIdeal.FG) :
    ∃ t : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n), Ideal.span (↑t : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) = I.toIdeal ∧
      ∀ f ∈ t, ∃ d : ℕ, f.IsHomogeneous d := by
  classical
  obtain ⟨s, hs⟩ := (Ideal.IsHomogeneous.iff_exists (Hilbert.Polynomial.GradedHilbert.grading R n) I.toIdeal).mp I.isHomogeneous
  have h : (Ideal.span (Subtype.val '' s)).FG := hs ▸ hfg
  obtain ⟨t, ht, he⟩ := Finite.IdealGenerators.fg_span_finite_subset (Subtype.val '' s) h
  refine ⟨t, he.trans hs.symm, ?_⟩
  intro f hf
  obtain ⟨g, _, rfl⟩ := ht hf
  exact g.property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FinitelyGeneratedHomogeneousIdeals.GradedHilbert
