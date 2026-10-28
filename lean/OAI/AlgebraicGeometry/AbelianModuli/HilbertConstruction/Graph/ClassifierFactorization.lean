import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifyingSourceIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterIsoCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationTransport

/-! # Classifier Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifierFactorization

noncomputable section

/-! A test-scheme morphism graph classified by a projective family satisfies the exact factorization-isomorphism condition over its parameter map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance classifierFactorPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))

local instance classifierFactorPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))

local instance classifierFactorPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

theorem graphClassifier_hasIsomorphicFactorization
    {S : Scheme.{u}} {T M : Over S} {A B : Over S} {n : ℕ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver M.left n)) (c : T ⟶ M)
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (he : F.projectiveBaseChange c.left = (MorphismGraphFamilies.morphismGraphFamily p).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j)) :
    FactorizationPointCondition.HasIsomorphicFactorization (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) F.inclusion
      (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)) c.left := by
  have hfirst : MorphismGraphFamilies.familyGraph p ≫ fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B) =
      𝟙 ((Over.pullback T.hom).obj A) := lift_fst (𝟙 _) p
  have : IsIso (MorphismGraphFamilies.familyGraph p ≫ fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B)) :=
    hfirst.symm ▸ inferInstance
  exact IsomorphicFactorizationTransport.hasIsomorphicFactorization_of_models c.left
    (ClassifyingSourceIso.graphClassifyingSourceIso F c.left (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) p he)
    (Product.ParameterBaseChange.productParameterBaseChangeIso c A B)
    (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n) c.left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c.left n))
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c A)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) F.inclusion (fst _ _)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) (MorphismGraphFamilies.familyGraph p ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) (fst _ _)
    (Product.ParameterIsoCompatibility.productParameterBaseChangeIso_embedding c j)
    (ClassifyingSourceIso.graphClassifyingSourceIso_embedding F c.left (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) p he)
    (Product.ParameterIsoCompatibility.productParameterBaseChangeIso_fst c A B) (MorphismGraphFamilies.familyGraph p) rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifierFactorization
