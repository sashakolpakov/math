import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionProductSegre
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.LineBundleSectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition

/-! # Tensor Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensoring an embedded line bundle with a globally generated line
bundle gives an actual closed projective embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem Generated.TensorEmbedding.tensorSectionMap_closedImmersion
    {X S : Scheme.{0}} (f : X ⟶ S) (L M : Line.Bundles.LineBundle X) {n m : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (t : Fin (m + 1) → (Line.Bundles.structureModule X ⟶ M.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i))
    (he : IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism f
      (Tensor.PairSectionFrames.tensorPairSectionFamily L M (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex n m)) s t)
      (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M
        (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex n m)) s t hs ht)).left := by
  let a := Relative.SectionProductSegre.relativeSectionProductMap f L M s t hs ht
  let p := (fst (Projective.ProjectivePresentations.projectiveSpaceOver S n) (Projective.ProjectivePresentations.projectiveSpaceOver S m)).left
  have hp : a.left ≫ p = (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left :=
    congrArg Over.Hom.left (lift_fst (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs)
      (SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht))
  let : IsSeparated p := inferInstanceAs
    (IsSeparated (pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom (Projective.ProjectivePresentations.projectiveSpaceOver S m).hom))
  let : IsClosedImmersion (a.left ≫ p) := (congrArg IsClosedImmersion hp).mpr he
  let : IsClosedImmersion a.left := IsClosedImmersion.of_comp a.left p
  have hc : IsClosedImmersion (a ≫ (Projective.Products.projectiveSpaceProductPresentation S n m).embedding).left :=
    inferInstanceAs (IsClosedImmersion
      (a.left ≫ (Projective.Products.projectiveSpaceProductPresentation S n m).embedding.left))
  exact (congrArg (fun k => IsClosedImmersion k.left)
    (Relative.SectionProductSegre.relativeSectionProductMap_segre f L M s t hs ht)).mp hc

variable {X S : Scheme.{0}} {f : X ⟶ S} {L : Line.Bundles.LineBundle X}

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.exists_addGeneratedPower (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) (m : ℕ)
    (hm : HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (L.tensorPower m).sheaf) :
    ∃ F : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f, F.degree = E.degree + m := by
  classical
  obtain ⟨ι, hι, t, ht⟩ := hm.lineBundle_section_cover (L.tensorPower m)
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let t' : Fin (Fintype.card ι + 1) → (Line.Bundles.structureModule X ⟶ (L.tensorPower m).sheaf) :=
    Fin.cases 0 (fun j => t (e.symm j))
  have ht' : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t' i) := by
    intro x
    obtain ⟨i, hi⟩ := ht x
    exact ⟨(e i).succ, by simpa only [t', Fin.cases_succ, Equiv.symm_apply_apply] using hi⟩
  let eP := (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some
  let c := Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex E.dimension (Fintype.card ι))
  refine ⟨{
    degree := E.degree + m
    degree_pos := Nat.add_pos_left E.degree_pos m
    power := E.power.tensor (L.tensorPower m)
    isPower := (L.tensorPower_isTensorPower (E.degree + m)).of_targetIso
      (L.tensorPowerAddIso E.degree m ≪≫ Tensor.ProductSheaf.tensorModuleCongr eP.symm (Iso.refl _))
    dimension := Affine.SegreOver.segreProjectiveDimension E.dimension (Fintype.card ι)
    sections := Tensor.PairSectionFrames.tensorPairSectionFamily E.power (L.tensorPower m) c E.sections t'
    covers := Tensor.PairSectionFrames.tensorPairSectionFamily_covers E.power (L.tensorPower m) c E.sections t' E.covers ht'
    closedImmersion := Generated.TensorEmbedding.tensorSectionMap_closedImmersion f E.power (L.tensorPower m)
      E.sections t' E.covers ht' E.closedImmersion }, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
