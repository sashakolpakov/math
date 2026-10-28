import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Unique Over Hom -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniqueOverHom

noncomputable section

/-! The unique map of schemes over a base has exactly the usual
unique underlying factorization property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem unique_over_hom_iff {S : Scheme.{0}} (T Z : Over S) :
    (∃! _f : T ⟶ Z, True) ↔ ∃! f : T.left ⟶ Z.left, f ≫ Z.hom = T.hom := by
  constructor
  · rintro ⟨f, _, hf⟩
    refine ⟨f.left, f.w, ?_⟩
    intro g hg
    exact congrArg Over.Hom.left (hf (Over.homMk g hg) trivial)
  · rintro ⟨f, hf, hu⟩
    refine ⟨Over.homMk f hf, trivial, ?_⟩
    intro g _
    exact Over.OverMorphism.ext (hu g.left g.w)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniqueOverHom
