import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Finite Surjective Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteSurjectiveDescent

noncomputable section

/-! A proper morphism is finite if it becomes finite after any surjective scheme base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_isFinite_of_surjective_baseChange
    {X Y Z P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (H : IsPullback a b f g) [IsProper f] [Surjective g] [IsFinite b] : IsFinite f := by
  have hfinite (y : Y) : (f ⁻¹' {y}).Finite := by
    obtain ⟨z, hz⟩ := g.surjective y
    apply ((b.finite_preimage (Set.finite_singleton z)).image a).subset
    intro x hx
    have hxy : f x = g z := hx.trans hz.symm
    obtain ⟨p, hp, hq⟩ := Scheme.exists_preimage_of_isPullback H x z hxy
    exact ⟨p, hq, hp⟩
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f hfinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteSurjectiveDescent
