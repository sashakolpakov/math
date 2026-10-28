import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

/-! # Parameter -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter

noncomputable section

/-! Geometric finiteness of the actual schemes returned by the full Presentations
inputs. Over a locally noetherian base the open graph locus is quasi-compact. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

def e34ProjectivePresentationOfNative {X : Over S} (B : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) :
    HilbertScheme.Presentations.Has.Core.ProjectivePresentation X where
  dimension := B.dimension
  embedding := B.embedding.left
  closed := B.closedImmersion
  over_base := B.embedding.w

def nativeProjectivePresentationOfPresentations {X : Over S} (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := B.dimension
  embedding := Over.homMk B.embedding B.over_base
  closedImmersion := B.closed

theorem e34ProjectivePresentation_proper {X : Over S} (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) :
    IsProper X.hom := (nativeProjectivePresentationOfPresentations B).proper

variable [IsLocallyNoetherian S] (X Y : Over S)
  [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
  {B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ Y)} {n : ℕ} {P : Fin n → Polynomial ℚ}
  (L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci X Y B n P)

theorem e34HomScheme_finiteType_separated :
    LocallyOfFiniteType L.homScheme.hom ∧ QuasiCompact L.homScheme.hom ∧
      IsSeparated L.homScheme.hom := by
  have : IsProper L.hilbert.hom := e34ProjectivePresentation_proper (Classical.choice L.projective)
  have : IsLocallyNoetherian L.hilbert.left := LocallyOfFiniteType.isLocallyNoetherian L.hilbert.hom
  have : IsOpenImmersion L.graphInclusion.left := L.graph_open
  refine ⟨L.hom_finiteType, ?_, ?_⟩ <;>
    rw [← L.graphInclusion.w] <;> infer_instance

variable (A : Over S) [GrpObj A] [Flat A.hom] [IsProper A.hom]
  [LocallyOfFinitePresentation A.hom]
  {BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A ⨯ A)}
  {LA : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A A BA n P}
  {R : HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A n}
  (M : HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A BA n P LA R)

theorem e34SolutionScheme_finiteType_separated :
    LocallyOfFiniteType M.solutionScheme.hom ∧ QuasiCompact M.solutionScheme.hom ∧
      IsSeparated M.solutionScheme.hom := by
  obtain ⟨hft, hqc, hsep⟩ := e34HomScheme_finiteType_separated A A LA
  have := hft
  have := hqc
  have := hsep
  have : IsClosedImmersion M.forgetGroup.left := M.group_closed
  have : IsClosedImmersion M.forgetEquations.left := M.equations_closed
  have h : M.solutionScheme.hom =
      M.forgetEquations.left ≫ M.forgetGroup.left ≫ LA.homScheme.hom := by
    rw [M.forgetGroup.w, M.forgetEquations.w]
  rw [h]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
