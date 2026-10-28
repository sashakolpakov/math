import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.ProductSegreMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismOpenFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PairSectionFrames

/-! # Product Segre Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProductSegreMorphism

noncomputable section

/-! The actual Segre morphism composed with the product of two
section-defined projective maps is the morphism defined by their tensor
product sections. The comparison holds over an arbitrary base scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} (f : X ⟶ S) (L M : Line.Bundles.LineBundle X)
variable {n m d : ℕ}
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
variable (t : Fin (m + 1) → (Line.Bundles.structureModule X ⟶ M.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (ht : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (t j))

def absoluteSectionProductMap : X ⟶
    pullback (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m).hom :=
  pullback.lift (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) (SectionsProjectiveMorphism.sectionAbsoluteMorphism f t ht)
    ((SectionsProjectiveMorphism.sectionAbsoluteMorphism_over f s hs).trans (SectionsProjectiveMorphism.sectionAbsoluteMorphism_over f t ht).symm)

theorem absoluteSectionProductMap_fst :
    absoluteSectionProductMap f L M s t hs ht ≫ pullback.fst _ _ =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs := pullback.lift_fst _ _ _

theorem absoluteSectionProductMap_snd :
    absoluteSectionProductMap f L M s t hs ht ≫ pullback.snd _ _ =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism f t ht := pullback.lift_snd _ _ _

variable (e : Segre.ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1))

theorem absoluteSectionProductMap_segre :
    (absoluteSectionProductMap f L M s t hs ht ≫ Segre.ProjectiveIsomorphism.affineSegreEmbedding (CommRingCat.of Γ(S, ⊤)) n m) ≫
      (Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤) e).hom.left =
    SectionsProjectiveMorphism.sectionAbsoluteMorphism f (Tensor.PairSectionFrames.tensorPairSectionFamily L M e s t)
      (Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M e s t hs ht) := by
  let q := Tensor.PairSectionFrames.tensorPairSectionFamily L M e s t
  let hq := Tensor.PairSectionFrames.tensorPairSectionFamily_covers L M e s t hs ht
  apply (SectionsProjectiveMorphism.sectionOpenCover q hq).hom_ext
  intro i
  let U := Ample.LineBundles.sectionNonvanishing (q i)
  have hqi : IsIso (Ample.LineBundles.pullbackSection U.ι (q i)) :=
    inferInstanceAs (IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (q i)).ι (q i)))
  have hp := (Tensor.SectionNonvanishing.tensorProductSection_pullback_isIso_iff U.ι L M
    (s (e.symm i).1.down) (t (e.symm i).2.down)).mp hqi
  let : IsIso (Ample.LineBundles.pullbackSection U.ι (s (e.symm i).1.down)) := hp.1
  let : IsIso (Ample.LineBundles.pullbackSection U.ι (t (e.symm i).2.down)) := hp.2
  let : Algebra Γ(S, ⊤) Γ(U.toScheme, ⊤) := (U.ι ≫ f).appTop.hom.toAlgebra
  let r := fun j => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (s (e.symm i).1.down))
    (Ample.LineBundles.pullbackSection U.ι (s j))
  let c := fun j => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (t (e.symm i).2.down))
    (Ample.LineBundles.pullbackSection U.ι (t j))
  have hr : r (e.symm i).1.down = 1 := Frame.Coordinates.frameCoordinate_self _
  have hc : c (e.symm i).2.down = 1 := Frame.Coordinates.frameCoordinate_self _
  have hprod : U.ι ≫ absoluteSectionProductMap f L M s t hs ht =
      Normalized.ProductSegreMap.normalizedProjectiveProductMap Γ(S, ⊤) (e.symm i) r c hr hc := by
    apply pullback.hom_ext
    · rw [Category.assoc, absoluteSectionProductMap_fst]
      change U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs =
        pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [pullback.lift_fst]
      exact MorphismOpenFrame.sectionAbsoluteMorphism_on_open_frame f s hs U (e.symm i).1.down
    · rw [Category.assoc, absoluteSectionProductMap_snd]
      change U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f t ht =
        pullback.lift _ _ _ ≫ pullback.snd _ _
      rw [pullback.lift_snd]
      exact MorphismOpenFrame.sectionAbsoluteMorphism_on_open_frame f t ht U (e.symm i).2.down
  have hcoords : ReindexedSegreEvaluation.reindexedSegreSectionCoordinates e r c =
      fun j => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (q i)) (Ample.LineBundles.pullbackSection U.ι (q j)) := by
    funext j
    exact (Tensor.PairSectionFrames.frameCoordinate_pullback_tensorProduct L M U.ι
      (s (e.symm i).1.down) (s (e.symm j).1.down)
      (t (e.symm i).2.down) (t (e.symm j).2.down)).symm
  calc
    _ = ((U.ι ≫ absoluteSectionProductMap f L M s t hs ht) ≫
        Segre.ProjectiveIsomorphism.affineSegreEmbedding (CommRingCat.of Γ(S, ⊤)) n m) ≫
        (Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤) e).hom.left := by
      simp only [Category.assoc]
      rfl
    _ = (Normalized.ProductSegreMap.normalizedProjectiveProductMap Γ(S, ⊤) (e.symm i) r c hr hc ≫
        Segre.ProjectiveIsomorphism.affineSegreEmbedding (CommRingCat.of Γ(S, ⊤)) n m) ≫
        (Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤) e).hom.left := by rw [hprod]
    _ = ProjectiveChart.Evaluation.projectiveChartMap (algebraMap Γ(S, ⊤) Γ(U.toScheme, ⊤))
        (ReindexedSegreEvaluation.reindexedSegreSectionCoordinates e r c) i
        (Segre.StandardChartEvaluation.reindexedSegreSectionCoordinates_pivot_inverse e i r c hr hc) :=
      Normalized.ProductSegreMap.normalizedProjectiveProductMap_segreStandard Γ(S, ⊤) r c e i hr hc
    _ = ProjectiveChart.Evaluation.projectiveChartMap (U.ι ≫ f).appTop.hom
        (fun j => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (q i)) (Ample.LineBundles.pullbackSection U.ι (q j))) i
        (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection U.ι (q i))) :=
      Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients rfl hcoords i _ _
    _ = U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hq :=
      (MorphismOpenFrame.sectionAbsoluteMorphism_on_open_frame f q hq U i).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProductSegreMorphism
