import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingCartesian

/-! # Graph Parameter Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphParameterCompatibility

noncomputable section

/-! The fixed product embedding pulled back to a test scheme agrees with its pullback through any Hilbert parameter map, as an actual Cartesian embedding diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {T M : Over S} {A B : Over S} {n : ℕ}
variable (f : T ⟶ M) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)

theorem relativeProjectiveGraphEmbedding_parameter_natural :
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n =
      Product.ParameterBaseChange.productParameterBaseChangeMap f A B ≫ (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j).left := by
  have h := Cartesian.BaseChangeNaturality.cartesianBaseChangeMap_natural f.left M.hom
    (Graph.FamilyNaturality.overProductBaseChangeMap T.hom A B) (Graph.FamilyNaturality.overProductBaseChangeMap M.hom A B)
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap M.hom n)
    (Product.ParameterBaseChange.parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)
    (Projective.ParameterBaseChange.projectiveParameter_composite_isPullback f n) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback M.hom n)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) j
    (GraphEmbeddingCartesian.relativeProjectiveGraphEmbedding_over T.hom j).symm (GraphEmbeddingCartesian.relativeProjectiveGraphEmbedding_over M.hom j).symm
  rw [Projective.ParameterBaseChange.projectiveParameterBaseChangeMap_eq] at h
  exact h.symm

theorem relativeProjectiveGraphEmbedding_parameter_isPullback :
    IsPullback (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j).left (Product.ParameterBaseChange.productParameterBaseChangeMap f A B)
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n) (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j).left := by
  have houter : IsPullback (Product.ParameterBaseChange.productParameterBaseChangeMap f A B)
      ((RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j).left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).hom)
      ((RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j).left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver M.left n).hom) f.left := by
    rw [(RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j).w, (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j).w]
    exact Product.ParameterBaseChange.productParameterBaseChangeMap_isPullback f A B
  exact (houter.of_bot (relativeProjectiveGraphEmbedding_parameter_natural f j).symm
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f.left n)).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphParameterCompatibility
