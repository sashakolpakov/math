import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsOpenEquality
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal

/-! # Cech Ambient Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechAmbientExtension

noncomputable section

/-! Ambient coordinates and cover refinements preserve the actual
supported-section edge, with the coefficient universe kept independent
of the underlying space. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.GlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type v} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type v} [LinearOrder ι] (W : ι → C) (O : Opens X)

local instance coefficient_limits [UnivLE.{v,z}] : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{v,v,z,u}
local instance coefficient_products [UnivLE.{v,z}] : HasProducts.{v} (ModuleCat.{z} R) :=
  fun J => by
    let : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) := ModuleCat.hasLimitsOfSize.{v,v,z,u}
    exact HasLimitsOfSize.has_limits_of_shape (Discrete J)
local instance coefficient_coproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun J => by
    let : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) := ModuleCat.hasColimitsOfSize.{z,u,0,0} R
    exact HasColimitsOfSize.has_colimits_of_shape (Discrete J)

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v z} R)) ℕ)

private theorem terminal_eq (A : Opens X) : (RelativeCech.Intersections.intersect A).obj (⊤_ (Opens X)) = A := by
  have ht : (⊤_ (Opens X)) = (⊤ : Opens X) :=
    le_antisymm le_top (leOfHom (terminal.from (⊤ : Opens X)))
  change A ⊓ (⊤_ (Opens X)) = A
  rw [ht, inf_top_eq]

def sourceIso : OrderedCechEdge.source.{u,v,v,z} R X F O K ≅
    OrderedCechEdge.source.{u,v,v,z} R X (RelativeCech.Intersections.intersect (F.obj (⊤_ C))) O K :=
  SectionsOpenEquality.complexIso O (F.obj (⊤_ C))
    ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).obj (⊤_ (Opens X)))
    (terminal_eq X (F.obj (⊤_ C))).symm K

variable (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)

include hglobal in
theorem relative_global : (RelativeCech.Intersections.intersect (F.obj (⊤_ C))).obj (⊤_ (Opens X)) ⊔ O = ⊤ := by
  rw [terminal_eq]
  exact hglobal

theorem extension : (sourceIso R X F O K).hom ≫
    SectionsExcision.extensionComplex O
      ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).obj (⊤_ (Opens X)))
      (relative_global X F O hglobal) K =
    SectionsExcision.extensionComplex O (F.obj (⊤_ C)) hglobal K :=
  SectionsOpenEquality.complex_extension O (F.obj (⊤_ C))
    ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).obj (⊤_ (Opens X)))
    (terminal_eq X (F.obj (⊤_ C))).symm K hglobal (relative_global X F O hglobal)

variable [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]

theorem ambient_component_extension (q : ℕ) :
    OrderedCechEdge.component.{u,v,v,z} R X F W O K q ≫
      (AugmentedCech.AmbientCoordinates.componentIso F W (K.X q).obj 0).hom =
    (SectionsExcision.extensionComplex O (F.obj (⊤_ C)) hglobal K).f q ≫
      RelativeCech.GlobalSections.relativeAugmentation (F.obj (⊤_ C)) (F.obj ∘ W) (K.X q).obj := by
  have he := SectionsExcision.extension_restriction O (F.obj (⊤_ C)) hglobal (K.X q)
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index ι 0)
  erw [Category.assoc, AugmentedCech.AmbientCoordinates.component_hom_π]
  erw [Category.assoc
    ((SectionsExcision.extensionComplex O (F.obj (⊤_ C)) hglobal K).f q)]
  erw [RelativeCech.GlobalSections.relativeAugmentation_projection]
  erw [← Category.assoc (OrderedCechEdge.component R X F W O K q)]
  change (((SectionsExcision.inclusion (F.obj (⊤_ C))
      (F.obj (⊤_ C) ⊓ O) inf_le_left).app (K.X q) ≫
        (AugmentedOrdered.CechZero.zeroIso W (F.op ⋙ (K.X q).obj)).inv) ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rw [← Category.assoc ((AugmentedOrdered.CechZero.zeroIso W (F.op ⋙ (K.X q).obj)).inv),
    AugmentedOrdered.CechZero.zeroIso_inv_π]
  rw [← he]
  simp only [Category.assoc]
  change _ ≫ ((K.X q).obj.map _ ≫ (K.X q).obj.map _ ≫ (K.X q).obj.map _) = _
  simp only [← Functor.map_comp]
  congr 2

include hglobal in
theorem ambient_component (q : ℕ) :
    OrderedCechEdge.component.{u,v,v,z} R X F W O K q ≫
      (AugmentedCech.AmbientCoordinates.componentIso F W (K.X q).obj 0).hom =
    (sourceIso R X F O K).hom.f q ≫
      OrderedCechEdge.component.{u,v,v,z} R X (RelativeCech.Intersections.intersect (F.obj (⊤_ C)))
        (F.obj ∘ W) O K q := by
  rw [Relative.SupportedExtension.local_component R X (F.obj (⊤_ C))
    (F.obj ∘ W) O K (relative_global X F O hglobal) q]
  have he := congrArg (fun a => a.f q) (extension R X F O K hglobal)
  change (sourceIso R X F O K).hom.f q ≫
    (SectionsExcision.extensionComplex O
      ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).obj (⊤_ (Opens X)))
      (relative_global X F O hglobal) K).f q = _ at he
  rw [← Category.assoc, he]
  exact ambient_component_extension R X F W O K hglobal q

variable (hW : ∀ i, F.obj (W i) ≤ O)

include hglobal in
theorem ambient_edge :
    OrderedCechEdge.map.{u,v,v,z} R X F W O K hW ≫
      (AugmentedCech.AmbientTotal.totalIso F W
        (Relative.SupportedExtension.underlying.{u,v,z} R X K)).hom =
    (sourceIso R X F O K).hom ≫
      OrderedCechEdge.map.{u,v,v,z} R X (RelativeCech.Intersections.intersect (F.obj (⊤_ C)))
        (F.obj ∘ W) O K (fun i => inf_le_right.trans (hW i)) := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, OrderedCechEdge.map,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f, AugmentedCech.AmbientTotal.totalIso,
    HomologicalComplex₂.total.mapIso_hom, Category.assoc, HomologicalComplex₂.ιTotal_map,
    AugmentedCech.AmbientTotal.bicomplexIso_hom_f]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ (RelativeCech.Total.source (F.obj (⊤_ C)) (F.obj ∘ W)
      (Relative.SupportedExtension.underlying.{u,v,z} R X K)).ιTotal (.up ℕ) q 0 q rfl)
      (ambient_component R X F W O K hglobal q))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechAmbientExtension
