import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleQuasiFinitePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationAmpleBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Quasi Projective Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuasiProjectiveAmpleness

noncomputable section

/-! An actual quasi-projective presentation over an affine Noetherian
base supplies an ample line bundle, by restricting the projective
compactification's twisting bundle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {B : Scheme.{u}} {X : Over B}

def quasiProjectiveAmpleLineBundle (P : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation X) : HilbertConstruction.Line.Bundles.LineBundle X.left :=
  P.projective.ampleLineBundle.pullback P.embedding.left

theorem quasiProjectiveAmpleLineBundle_isAmple [IsAffine B] [IsNoetherian B]
    (P : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation X) : (quasiProjectiveAmpleLineBundle P).IsAmple := by
  have : IsNoetherian X.left := P.noetherian
  have : TopologicalSpace.NoetherianSpace X.left := IsNoetherian.noetherianSpace
  have : QuasiCompact P.embedding.left := by
    constructor
    intro U _ _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have : IsProper P.compactification.hom := P.projective.proper
  have : P.compactification.left.IsSeparated := ⟨by
    rw [← terminal.comp_from P.compactification.hom]
    infer_instance⟩
  exact AmpleQuasiFinitePullback.ample_pullback_openImmersion P.embedding.left
    P.projective.ampleLineBundle P.projective.ampleLineBundle_isAmple

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuasiProjectiveAmpleness
