import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicHomFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

/-! # Polarized Isomorphisms Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedIsomorphismsFinite

noncomputable section

/-! Polarized full-level isomorphisms with a fixed embedded graph polynomial form a finite set over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {K : Type u} [Field K] {g N n : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
variable [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem boundedPolarizedIsomorphisms_finite :
    Finite {e : Moduli.Isomorphisms.LevelPreservingIso A B // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P e.abelian.hom} := by
  have := IntrinsicHomFinite.boundedNativeAbelianHom_finite A.abelian B.abelian j P
  let f : {e : Moduli.Isomorphisms.LevelPreservingIso A B // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P e.abelian.hom} →
      {p : A.abelian.scheme ⟶ B.abelian.scheme // IsMonHom p ∧ Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p} :=
    fun e => ⟨e.val.abelian.hom, e.val.abelianGroup, e.property⟩
  apply Finite.of_injective f
  intro e d h
  apply Subtype.ext
  exact Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e.val d.val (congrArg Subtype.val h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedIsomorphismsFinite
