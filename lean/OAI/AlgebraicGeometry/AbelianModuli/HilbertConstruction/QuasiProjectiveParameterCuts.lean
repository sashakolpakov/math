import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveImmersions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Quasi Projective Parameter Cuts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Closed parameter cuts and open subsets retain actual quasi-projective presentations over a noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {S : Scheme.{u}} {X Y : Over S}

theorem Projective.ProjectivePresentations.QuasiProjectivePresentation.noetherian (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) [IsNoetherian S] :
    IsNoetherian X.left := by
  have : LocallyOfFiniteType X.hom := Q.locallyFiniteType
  have : QuasiCompact X.hom := Q.quasiCompact
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨⟩

def Projective.ProjectivePresentations.QuasiProjectivePresentation.ofClosedImmersion (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X)
    [IsNoetherian S] (j : Y ⟶ X) [IsClosedImmersion j.left] : Projective.ProjectivePresentations.QuasiProjectivePresentation Y := by
  have : IsNoetherian X.left := Q.noetherian
  have : NoetherianSpace X.left := IsNoetherian.noetherianSpace
  have : QuasiCompact Q.embedding.left := inferInstance
  have : IsImmersion (j ≫ Q.embedding).left :=
    inferInstanceAs (IsImmersion (j.left ≫ Q.embedding.left))
  have : QuasiCompact (j ≫ Q.embedding).left :=
    inferInstanceAs (QuasiCompact (j.left ≫ Q.embedding.left))
  exact Q.projective.quasiProjectiveImmersion (j ≫ Q.embedding)

def Projective.ProjectivePresentations.QuasiProjectivePresentation.openParameter (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X)
    [IsNoetherian S] (U : X.left.Opens) : Projective.ProjectivePresentations.QuasiProjectivePresentation (Open.ParameterPoints.openParameterScheme X U) := by
  have : IsNoetherian X.left := Q.noetherian
  have : NoetherianSpace X.left := IsNoetherian.noetherianSpace
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X.left)
  have : QuasiCompact U.ι := inferInstance
  have : LocallyOfFiniteType X.hom := Q.locallyFiniteType
  have : QuasiCompact X.hom := Q.quasiCompact
  refine
    { locallyFiniteType := ?_
      quasiCompact := ?_
      compactification := Q.compactification
      projective := Q.projective
      embedding := Open.ParameterPoints.openParameterInclusion X U ≫ Q.embedding
      openImmersion := ?_ }
  · change LocallyOfFiniteType (U.ι ≫ X.hom)
    infer_instance
  · change QuasiCompact (U.ι ≫ X.hom)
    infer_instance
  · change IsOpenImmersion (U.ι ≫ Q.embedding.left)
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
