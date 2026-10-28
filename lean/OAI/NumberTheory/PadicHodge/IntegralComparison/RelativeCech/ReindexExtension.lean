import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexData
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexCoordinates

/-! # Reindex Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexExtension

noncomputable section

/-! The literal relative Cech extension, including its signs and the
zero components outside the distinguished chart, commutes with inverse image. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
attribute [local instance] ReindexData.preimage_limits
variable (U : Opens X) {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (P : (Opens Y)ᵒᵖ ⥤ A)

def sourceFactorIso {n : ℕ} (a : AugmentedOrdered.Cech.Index ι n) :
    (ReindexData.preimage f).obj (U ⊓ (AugmentedOrdered.Cech.formal V n).obj a) ≅
      (ReindexData.preimage f).obj U ⊓ (AugmentedOrdered.Cech.formal ((ReindexData.preimage f).obj ∘ V) n).obj a :=
  (Intersections.intersect ((ReindexData.preimage f).obj U)).mapIso (PreservesProduct.iso (ReindexData.preimage f) (V ∘ a.val))

def targetFactorIso {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n+1)) :
    (ReindexData.preimage f).obj ((AugmentedOrdered.Cech.formal (Intersections.cover U V) (n+1)).obj a) ≅
      (AugmentedOrdered.Cech.formal (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V)) (n+1)).obj a :=
  OrderedCech.ReindexCoordinates.familyFactorIso (ReindexData.preimage f) (Intersections.cover U V)
    (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V)) (ReindexData.cover_eq f U V) a

omit [HasCoproducts A] in
theorem source_projection {n : ℕ} (a : AugmentedOrdered.Cech.Index ι n) :
    (ReindexData.sourceIso f U V P).hom.f n ≫
      ExtensionComponents.sourceProjection ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P a =
    ExtensionComponents.sourceProjection U V ((ReindexData.preimage f).op ⋙ P) a ≫ P.map (sourceFactorIso f U V a).inv.op := by
  change (AugmentedOrdered.CechReindex.componentIso (ReindexData.preimage f) V
    (Intersections.presheaf ((ReindexData.preimage f).obj U) P) n).hom ≫ _ = _
  exact AugmentedOrdered.CechReindex.component_hom_π (ReindexData.preimage f) V
    (Intersections.presheaf ((ReindexData.preimage f).obj U) P) n a

omit [HasCoproducts A] in
theorem target_projection {n : ℕ} (a : AugmentedOrdered.Cech.Index (WithBot ι) (n+1)) :
    (ReindexData.targetIso f U V P).hom.f n ≫
      ExtensionComponents.targetProjection ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P a =
    ExtensionComponents.targetProjection U V ((ReindexData.preimage f).op ⋙ P) a ≫ P.map (targetFactorIso f U V a).inv.op := by
  have h := OrderedCech.ReindexCoordinates.family_hom_f (ReindexData.preimage f) (Intersections.cover U V)
    (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V)) (ReindexData.cover_eq f U V) P n
  change (ReindexData.targetIso f U V P).hom.f n = _ at h
  rw [h]
  exact Pi.mapIso_hom_π _ _

omit [HasCoproducts A] in
theorem target_naturality {Q : (Opens Y)ᵒᵖ ⥤ A} (a : P ⟶ Q) :
    OrderedCech.Functor.Projection.complexMap (Intersections.cover U V) (Functor.whiskerLeft (ReindexData.preimage f).op a) ≫
      (ReindexData.targetIso f U V Q).hom =
    (ReindexData.targetIso f U V P).hom ≫ OrderedCech.Functor.Projection.complexMap
      (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V)) a :=
  OrderedCech.ReindexCoordinates.family_naturality (ReindexData.preimage f) (Intersections.cover U V)
    (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V)) (ReindexData.cover_eq f U V) P a

omit [HasCoproducts A] in
theorem extension :
    ExtensionDifferential.map U V ((ReindexData.preimage f).op ⋙ P) ≫ (ReindexData.targetIso f U V P).hom =
      (ReindexData.sourceIso f U V P).hom ≫ ExtensionDifferential.map
        ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index (WithBot ι) (n+1))
  change (ExtensionComponents.component U V ((ReindexData.preimage f).op ⋙ P) n ≫ (ReindexData.targetIso f U V P).hom.f n) ≫
      ExtensionComponents.targetProjection ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P a =
    ((ReindexData.sourceIso f U V P).hom.f n ≫ ExtensionComponents.component ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P n) ≫
      ExtensionComponents.targetProjection ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P a
  rw [Category.assoc, target_projection, ← Category.assoc,
    Category.assoc ((ReindexData.sourceIso f U V P).hom.f n)]
  by_cases h : a.val 0 = ⊥
  · rw [ExtensionComponents.component_bot U V ((ReindexData.preimage f).op ⋙ P) a h,
      ExtensionComponents.component_bot ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P a h,
      zsmul_comp, comp_zsmul, ← Category.assoc, source_projection]
    simp only [Category.assoc]
    apply congrArg (fun b => (-1 : ℤ)^n • (ExtensionComponents.sourceProjection U V ((ReindexData.preimage f).op ⋙ P) (Indices.tail a h) ≫ b))
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    exact (P.map_comp _ _).symm.trans
      ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))
  · rw [ExtensionComponents.component_ne_bot U V ((ReindexData.preimage f).op ⋙ P) a h,
      ExtensionComponents.component_ne_bot ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) P a h, zero_comp, comp_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexExtension
