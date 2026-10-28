import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Source Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteSourceCover

noncomputable section

/-! A proper morphism is finite when its composite with a surjective source map is finite. Finite fibers are the images of the actual composite fibers. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem proper_isFinite_of_surjective_precomp {W X Y : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ Y) [Surjective p] [IsProper f] [IsFinite (p ≫ f)] : IsFinite f := by
  have hf (y : Y) : (f ⁻¹' {y}).Finite := by
    apply (((p ≫ f).finite_preimage (Set.finite_singleton y)).image p).subset
    intro x hx
    obtain ⟨w, rfl⟩ := p.surjective x
    exact ⟨w, hx, rfl⟩
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f hf
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteSourceCover
