import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LineBundleSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveHomogeneousPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite

/-! # Line Bundle Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Line-bundle section finiteness descends through actual homogeneous presentations of arbitrary closed projective embeddings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable {X : Over (Spec (.of R))}

theorem Closed.LineBundleSectionFiniteness.ClosedProjectiveEmbedding.lineBundleSections_finite
    (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left] (L : Line.Bundles.LineBundle X.left) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj L.sheaf) := by
  let e := Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hf : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i)).hom).obj
      (L.pullback e.hom.left).sheaf) :=
    Projective.LineBundleSectionFiniteness.projective_lineBundle_sections_finite (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) (L.pullback e.hom.left)
  let E := (Global.SectionsSchemeIso.schemeGlobalSectionsPullbackIso e.hom.left X.hom L.sheaf).trans
    (Intrinsic.LineBundleSections.schemeGlobalSectionsBaseCongr e.hom.w (L.pullback e.hom.left).sheaf)
  exact @Module.Finite.equiv R _ _ _ _ _ _ _ hf E.symm

theorem Closed.LineBundleSectionFiniteness.relativeClosedEmbedding_lineBundleSections_finite
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n) [IsClosedImmersion i.left] (L : Line.Bundles.LineBundle X.left) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj L.sheaf) :=
  Closed.LineBundleSectionFiniteness.ClosedProjectiveEmbedding.lineBundleSections_finite (RelativeProjective.TwistingSectionsFinite.relativeEmbeddingAffineMap i) L

theorem Projective.ProjectivePresentations.ProjectivePresentation.lineBundleSections_finite
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (L : Line.Bundles.LineBundle X.left) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj L.sheaf) :=
  Closed.LineBundleSectionFiniteness.relativeClosedEmbedding_lineBundleSections_finite P.embedding L

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
