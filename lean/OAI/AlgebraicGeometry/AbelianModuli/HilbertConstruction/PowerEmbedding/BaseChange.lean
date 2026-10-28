import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionDataBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.Sections

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.BaseChange.PowerProjectiveEmbedding

noncomputable section

/-! Base change of a power embedding retains its actual sections,
degree and dimension, and a universally complete family stays complete. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem sectionData_closed
    {S : Scheme.{u}} {X : Over S} {P : Projective.ProjectivePresentations.ProjectivePresentation X}
    {L : Line.Bundles.LineBundle X.left} (D : P.SectionData L) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom D.sections D.covers).left :=
  (congrArg (fun a : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S P.dimension => IsClosedImmersion a.left)
    D.embedding_eq).mp P.closedImmersion

variable {S T : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (f : T ⟶ S)
    (M : Line.Bundles.LineBundle ((Over.pullback f).obj X).left)
    (eM : M.sheaf ≅ (L.pullback (pullback.fst X.hom f)).sheaf)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.baseChangeWithLineIso : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding M ((Over.pullback f).obj X).hom := by
  let p := pullback.fst X.hom f
  let D := E.sectionData.baseChange f
  exact {
    degree := E.degree
    degree_pos := E.degree_pos
    power := E.power.pullback p
    isPower := (M.tensorPower_isTensorPower E.degree).of_targetIso
      ((TensorPower.Maps.tensorPowerFunctor ((Over.pullback f).obj X).left E.degree).mapIso eM ≪≫
        (L.powerBaseChangeIso p E.degree).symm ≪≫
          (Scheme.Modules.pullback p).mapIso
            (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some.symm)
    dimension := E.dimension
    sections := D.sections
    covers := D.covers
    closedImmersion := sectionData_closed D }

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.baseChangeWithLineIso_degree : (E.baseChangeWithLineIso f M eM).degree = E.degree := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.baseChangeWithLineIso_dimension : (E.baseChangeWithLineIso f M eM).dimension = E.dimension := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.baseChangeWithLineIso_embedding :
    (E.baseChangeWithLineIso f M eM).projectivePresentation.embedding =
      (E.projectivePresentation.baseChange f).embedding :=
  (E.sectionData.baseChange f).embedding_eq.symm

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.completeBaseChangeData [IsAffine T]
    (h : Universal.SectionCompletenessOpen.UniversallyCompleteSectionFamily X.hom E.power.sheaf E.sections (𝟙 S)) :
    (E.baseChangeWithLineIso f M eM).CompleteSectionData := by
  let p := pullback.fst X.hom f
  let q := pullback.snd X.hom f
  let s := fun i => Ample.LineBundles.pullbackSection p (E.sections i)
  have hc : Function.Bijective
      (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q.appTop.hom (E.power.pullback p).sheaf s) := by
    have hs := h T f
    change Function.Bijective
      (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd X.hom (f ≫ 𝟙 S)).appTop.hom
        ((Scheme.Modules.pullback (pullback.fst X.hom (f ≫ 𝟙 S))).obj E.power.sheaf)
        (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom (f ≫ 𝟙 S)) (E.sections i))) at hs
    rw [Category.comp_id] at hs
    exact hs
  exact {
    basis := Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective q.appTop.hom (E.power.pullback p).sheaf s hc
    sections_eq := (Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective_family q.appTop.hom
      (E.power.pullback p).sheaf s hc).symm }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.BaseChange.PowerProjectiveEmbedding
