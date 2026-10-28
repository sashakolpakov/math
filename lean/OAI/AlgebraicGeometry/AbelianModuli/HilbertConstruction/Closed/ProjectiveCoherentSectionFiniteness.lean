import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.PullbackIsoFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.LineBundleSectionFiniteness

/-! # Projective Coherent Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite sections for coherent sheaves on arbitrary projective presentations over a Noetherian affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable {X : Over (Spec (.of R))}

theorem Closed.ProjectiveCoherentSectionFiniteness.ClosedProjectiveEmbedding.coherentSections_finite
    (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj M) := by
  let e := Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  let N := (Scheme.Modules.pullback e.hom.left).obj M
  have hNq : N.IsQuasicoherent := Quasicoherent.PullbackIsoFiniteness.module_openPullback_quasicoherent e.hom.left M
  have hNt : N.IsFiniteType := Quasicoherent.PullbackIsoFiniteness.module_openPullback_finiteType e.hom.left M
  have hf : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i)).hom).obj N) :=
    @Projective.CoherentSectionFiniteness.projective_coherent_sections_finite R _ _ n (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) N hNq hNt
  let E := (Global.SectionsSchemeIso.schemeGlobalSectionsPullbackIso e.hom.left X.hom M).trans
    (Intrinsic.LineBundleSections.schemeGlobalSectionsBaseCongr e.hom.w N)
  exact @Module.Finite.equiv R _ _ _ _ _ _ _ hf E.symm

theorem Closed.ProjectiveCoherentSectionFiniteness.relativeClosedEmbedding_coherentSections_finite
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj M) :=
  Closed.ProjectiveCoherentSectionFiniteness.ClosedProjectiveEmbedding.coherentSections_finite (RelativeProjective.TwistingSectionsFinite.relativeEmbeddingAffineMap i) M

theorem Projective.ProjectivePresentations.ProjectivePresentation.coherentSections_finite
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj M) :=
  Closed.ProjectiveCoherentSectionFiniteness.relativeClosedEmbedding_coherentSections_finite P.embedding M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
