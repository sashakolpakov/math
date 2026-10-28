import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverIsoNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphParameterCompatibility

/-! # Parameter Iso Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterIsoCompatibility

noncomputable section

/-! Product comparison isomorphisms preserve source projection and the fixed relative projective embedding across parameter maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem productParameterBaseChangeIso_fst {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A B : Over S) :
    (ParameterBaseChange.productParameterBaseChangeIso f A B).hom ≫
      (Over.pullback f.left).map (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)) =
        fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B) ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom :=
  Cartesian.OverIsoNaturality.cartesianAmbientOverIso_natural f.left (ParameterBaseChange.productParameterBaseChangeMap f A B) (Single.ParameterBaseChange.singleParameterBaseChangeMap f A)
    (ParameterBaseChange.productParameterBaseChangeMap_isPullback f A B) (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback f A)
    (fst _ _) (fst _ _) (ParameterProjections.productParameterBaseChangeMap_fst f A B)

theorem productParameterBaseChangeIso_embedding {S : Scheme.{u}} {T M : Over S} {A B : Over S} {n : ℕ}
    (f : T ⟶ M) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) :
    (ParameterBaseChange.productParameterBaseChangeIso f A B).hom ≫ (Over.pullback f.left).map (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) =
      RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j ≫
        (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n) f.left
          (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f.left n)).hom :=
  Cartesian.OverIsoNaturality.cartesianAmbientOverIso_natural f.left (ParameterBaseChange.productParameterBaseChangeMap f A B) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n)
    (ParameterBaseChange.productParameterBaseChangeMap_isPullback f A B) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f.left n)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j)
    (Relative.GraphParameterCompatibility.relativeProjectiveGraphEmbedding_parameter_natural f j).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterIsoCompatibility
