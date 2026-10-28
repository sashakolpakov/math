import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicGeometry.Scheme

/-! # Over Locus Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverLocusClassification

noncomputable section

/-! Unique factorization over a fixed base is equivalent to the actual
scheme factorization with its automatically forced structural map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem over_existsUnique_lift_iff {S : Scheme.{0}} {T Z M : Over S}
    (j : Z ⟶ M) (x : T ⟶ M) :
    (∃! f : T ⟶ Z, f ≫ j = x) ↔ ∃! f : T.left ⟶ Z.left, f ≫ j.left = x.left := by
  have lift (f : T.left ⟶ Z.left) (hf : f ≫ j.left = x.left) : f ≫ Z.hom = T.hom := by
    rw [← j.w, ← Category.assoc, hf]
    exact x.w
  constructor
  · rintro ⟨f, hf, hu⟩
    refine ⟨f.left, congrArg Over.Hom.left hf, ?_⟩
    intro g hg
    exact congrArg Over.Hom.left (hu (Over.homMk g (lift g hg)) (Over.OverMorphism.ext hg))
  · rintro ⟨f, hf, hu⟩
    refine ⟨Over.homMk f (lift f hf), Over.OverMorphism.ext hf, ?_⟩
    intro g hg
    exact Over.OverMorphism.ext (hu g.left (congrArg Over.Hom.left hg))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverLocusClassification
