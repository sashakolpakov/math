import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.HomologyCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.HomologyComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.SheafGlobalCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass

/-! # Survivor Cech Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.SurvivorCechEdge

noncomputable section

/-! The actual single-survivor global edge has the original
CechZeroSections normalization after every native/additive coordinate map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (M : X.Modules) (c : ℕ)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections.moduleSingle M c
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechConcentration.coefficients K
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates.underlying AddCommGrpCat X
  (Principal.SingleAdditiveSections.sheafSingle M c)
local notation "j" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass.singleCoefficientIso M c
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation.sections π
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision.sections (D := AddCommGrpCat) (⊤ : X.Opens)

def singleIso := homologyMapIso
  (HomologicalComplex₂.total.mapIso
    (((OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).mapIso j) (.up ℕ)) c

def sectionsIso := homologyMapIso
  (((((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : X.Opens))).mapHomologicalComplex
    (.up ℕ)).mapIso j)) c

omit [X.IsSeparated] in
theorem single_edge :
    homologyMap (Presheaf.OrderedCechEdge.edge U Q) c ≫ (singleIso U M c).inv =
      (sectionsIso M c).inv ≫ homologyMap (Presheaf.OrderedCechEdge.edge U P) c := by
  have h := congrArg (fun f => homologyMap f c)
    (Ordered.EdgeNaturality.naturality U (j).hom)
  rw [homologyMap_comp, homologyMap_comp] at h
  apply (cancel_epi (sectionsIso M c).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (singleIso U M c).inv) h.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (homologyMap (Presheaf.OrderedCechEdge.edge U P) c ≫ ·)
          (singleIso U M c).hom_inv_id).trans (Category.comp_id _))))

omit [X.IsSeparated] in
theorem coefficient_edge :
    homologyMap (Presheaf.OrderedCechEdge.edge U P) c ≫
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K c).inv =
    (IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates.sectionIso π K c).inv ≫
      (G).map (homologyMap (IntrinsicOrdered.SingleEdge.Intrinsic.edge π U hU M c) c) := by
  apply (cancel_epi (IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates.sectionIso π K c).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have h := IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates.homology_coordinates π U hU K c
  exact (congrArg (· ≫ (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K c).inv) h.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg ((G).map (homologyMap (IntrinsicOrdered.SingleEdge.Intrinsic.edge π U hU M c) c) ≫ ·)
        (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K c).hom_inv_id).trans (Category.comp_id _)))

omit [X.IsSeparated] in
theorem source_coordinate :
    (sectionsIso M c).inv ≫ (IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates.sectionIso π K c).inv ≫
      (G).map (Functor.SingleEdge.sourceIso E M c).hom =
    (Functor.SingleEdge.sourceIso T (Closed.SupportedSurvivor.sheaf M) c).hom := by
  have hc := HomologyCoefficient.source G E M c
  have hs := HomologyComposition.coordinate
    (SheafOfModules.toSheaf X.ringCatSheaf) T M c
  calc
    _ = (sectionsIso M c).inv ≫ (Functor.SingleEdge.sourceIso (E ⋙ G) M c).hom :=
      congrArg ((sectionsIso M c).inv ≫ ·) hc
    _ = _ := by
      exact (congrArg ((sectionsIso M c).inv ≫ ·) hs.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (Functor.SingleEdge.sourceIso T (Closed.SupportedSurvivor.sheaf M) c).hom)
            (sectionsIso M c).inv_hom_id).trans (Category.id_comp _)))

omit [X.IsSeparated] in
theorem normalization :
    homologyMap (Presheaf.OrderedCechEdge.edge U Q) c ≫
      (singleIso U M c).inv ≫
        (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K c).inv ≫
          (G).map (IntrinsicOrdered.SingleEdge.Intrinsic.columnIso π U M c).hom =
    (SheafGlobalCohomology.iso π U hU M c).hom := by
  have hn := congrArg (G).map (IntrinsicOrdered.SingleEdge.Intrinsic.normalization π U hU M c)
  rw [(G).map_comp, (G).map_comp] at hn
  calc
    _ = (sectionsIso M c).inv ≫
        (homologyMap (Presheaf.OrderedCechEdge.edge U P) c ≫
          (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K c).inv) ≫
            (G).map (IntrinsicOrdered.SingleEdge.Intrinsic.columnIso π U M c).hom := by
      simpa only [Category.assoc] using congrArg
        (fun a => a ≫ (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K c).inv ≫
          (G).map (IntrinsicOrdered.SingleEdge.Intrinsic.columnIso π U M c).hom) (single_edge U M c)
    _ = ((sectionsIso M c).inv ≫ (IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates.sectionIso π K c).inv) ≫
        ((G).map (homologyMap (IntrinsicOrdered.SingleEdge.Intrinsic.edge π U hU M c) c) ≫
          (G).map (IntrinsicOrdered.SingleEdge.Intrinsic.columnIso π U M c).hom) := by
      simpa only [Category.assoc] using congrArg (fun a => (sectionsIso M c).inv ≫ a ≫
        (G).map (IntrinsicOrdered.SingleEdge.Intrinsic.columnIso π U M c).hom) (coefficient_edge π U hU M c)
    _ = ((sectionsIso M c).inv ≫ (IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates.sectionIso π K c).inv) ≫
        ((G).map (Functor.SingleEdge.sourceIso E M c).hom ≫
          (G).map (Cech.ZeroSections.iso π U hU M).hom) := congrArg (_ ≫ ·) hn
    _ = _ := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (G).map (Cech.ZeroSections.iso π U hU M).hom)
          (by simpa only [Category.assoc] using source_coordinate π M c))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.SurvivorCechEdge
