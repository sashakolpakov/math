import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationAmpleBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.QuasiProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleQuasiFinitePullback

/-! # Quasi Finite Quasi Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A separated quasi-finite finite-type parameter over a supplied
quasi-projective scheme is quasi-projective over the original affine
Noetherian base. The quasi-finite hypothesis concerns the parameter map,
not the structure morphism to that original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherian S] {X Y : Over S}

def Projective.ProjectivePresentations.QuasiProjectivePresentation.ampleLineBundle (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) :
    Line.Bundles.LineBundle X.left := Q.projective.ampleLineBundle.pullback Q.embedding.left

theorem Projective.ProjectivePresentations.QuasiProjectivePresentation.ampleLineBundle_isAmple (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) :
    Q.ampleLineBundle.IsAmple := by
  let : IsNoetherian X.left := Q.noetherian
  let : TopologicalSpace.NoetherianSpace X.left := IsNoetherian.noetherianSpace
  let : QuasiCompact Q.embedding.left := inferInstance
  let : IsProper Q.compactification.hom := Q.projective.proper
  let : Q.compactification.left.IsSeparated := ⟨by
    rw [← terminal.comp_from Q.compactification.hom]
    infer_instance⟩
  exact ReferenceFamily.AmpleQuasiFinitePullback.ample_pullback_openImmersion Q.embedding.left
    Q.projective.ampleLineBundle Q.projective.ampleLineBundle_isAmple

theorem Projective.ProjectivePresentations.QuasiProjectivePresentation.quasiFiniteSource_nonempty
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) (f : Y ⟶ X)
    [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left]
    [IsSeparated f.left] [QuasiCompact f.left] :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation Y) := by
  let : LocallyOfFiniteType X.hom := Q.locallyFiniteType
  let : IsSeparated X.hom := Q.separated
  let : X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from X.hom]
    infer_instance⟩
  let : LocallyOfFiniteType Y.hom := by
    rw [← f.w]
    infer_instance
  let : IsSeparated Y.hom := by
    rw [← f.w]
    infer_instance
  let : Y.left.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.hom]
    infer_instance⟩
  exact (ReferenceFamily.AmpleQuasiFinitePullback.ample_pullback_separated_quasiFinite f.left
    Q.ampleLineBundle Q.ampleLineBundle_isAmple).exists_quasiProjectivePresentation Y.hom

def Projective.ProjectivePresentations.QuasiProjectivePresentation.quasiFiniteSource
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) (f : Y ⟶ X)
    [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left]
    [IsSeparated f.left] [QuasiCompact f.left] : Projective.ProjectivePresentations.QuasiProjectivePresentation Y :=
  (Q.quasiFiniteSource_nonempty f).some

def Projective.ProjectivePresentations.QuasiProjectivePresentation.monomorphismSource
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) (f : Y ⟶ X)
    [LocallyOfFiniteType f.left] [QuasiCompact f.left] [Mono f.left] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation Y := by
  let : LocallyQuasiFinite f.left := UnramifiedQuasiFinite.locallyQuasiFinite_of_unramified f.left
  exact Q.quasiFiniteSource f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
