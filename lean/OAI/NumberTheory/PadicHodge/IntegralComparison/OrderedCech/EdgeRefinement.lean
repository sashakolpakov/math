import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement

/-! # Edge Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.EdgeRefinement

noncomputable section

/-! Full ordered Čech refinement preserves the literal global-section
edge, including its degree-zero augmentation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge
variable {X : TopCat.{u}}
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → Opens X) (V : κ → Opens X)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]

omit [HasCoproducts D] in
theorem augmentation_eq (P : (Opens X)ᵒᵖ ⥤ D) :
    Presheaf.OrderedCechEdge.augmentation U P = P.map (homOfLE (le_top : (⊤_ Opens X) ≤ ⊤)).op ≫
      (AugmentedOrdered.CechZero.zeroIso U P).inv ≫ AugmentedOrdered.Cech.differential U P 0 := by
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index ι 1)
  change Presheaf.OrderedCechEdge.augmentation U P ≫ Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 => P.obj (op ((AugmentedOrdered.Cech.formal U 1).obj b))) a =
    (P.map (homOfLE (le_top : (⊤_ Opens X) ≤ ⊤)).op ≫ (AugmentedOrdered.CechZero.zeroIso U P).inv ≫ AugmentedOrdered.Cech.differential U P 0) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 => P.obj (op ((AugmentedOrdered.Cech.formal U 1).obj b))) a
  erw [Presheaf.OrderedCechEdge.augmentation_projection, Category.assoc, Category.assoc,
    AugmentedOrdered.CechZero.zeroIso_inv_differential_π, ← P.map_comp]
  congr 1

omit [HasCoproducts D] in
theorem augmentation_refinement (P : (Opens X)ᵒᵖ ⥤ D) :
    Presheaf.OrderedCechEdge.augmentation U P ≫ (Refinement.map U V r P).f 0 = Presheaf.OrderedCechEdge.augmentation V P := by
  have h := (AugmentedOrdered.CechRefinement.map U V r P).comm 0 1
  rw [show (AugmentedOrdered.Cech.complex V P).d 0 1 = AugmentedOrdered.Cech.differential V P 0 from
    CochainComplex.of_d (AugmentedOrdered.Cech.object V P) (AugmentedOrdered.Cech.differential V P) 0,
    show (AugmentedOrdered.Cech.complex U P).d 0 1 = AugmentedOrdered.Cech.differential U P 0 from
    CochainComplex.of_d (AugmentedOrdered.Cech.object U P) (AugmentedOrdered.Cech.differential U P) 0] at h
  simp only [
    AugmentedOrdered.CechRefinement.map_f_zero,
    AugmentedOrdered.CechRefinement.map_f_succ] at h
  change ((AugmentedOrdered.CechZero.zeroIso U P).hom ≫ (AugmentedOrdered.CechZero.zeroIso V P).inv) ≫ AugmentedOrdered.Cech.differential V P 0 =
    AugmentedOrdered.Cech.differential U P 0 ≫ (Refinement.map U V r P).f 0 at h
  have hh := congrArg ((AugmentedOrdered.CechZero.zeroIso U P).inv ≫ ·) h
  rw [augmentation_eq, augmentation_eq]
  have ht := congrArg (P.map (homOfLE (le_top : (⊤_ Opens X) ≤ ⊤)).op ≫ ·) hh.symm
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using ht

theorem edge (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) :
    Presheaf.OrderedCechEdge.edge U K ≫ Refinement.totalMap U V r K =
      Presheaf.OrderedCechEdge.edge V K := by
  have h := BicomplexHorizontalEdge.naturality
    (Presheaf.OrderedCechEdge.bicomplex U K) (Presheaf.OrderedCechEdge.sections K) (fun q => Presheaf.OrderedCechEdge.augmentation U (K.X q))
    (fun q q' _ => Presheaf.OrderedCechEdge.augmentation_comm U K q q') (Presheaf.OrderedCechEdge.augmentation_cocycle U K)
    (Presheaf.OrderedCechEdge.bicomplex V K) (Presheaf.OrderedCechEdge.sections K) (fun q => Presheaf.OrderedCechEdge.augmentation V (K.X q))
    (fun q q' _ => Presheaf.OrderedCechEdge.augmentation_comm V K q q') (Presheaf.OrderedCechEdge.augmentation_cocycle V K)
    (Refinement.bicomplexMap U V r K) (𝟙 _) (fun q => by
      change Presheaf.OrderedCechEdge.augmentation U (K.X q) ≫ (Refinement.map U V r (K.X q)).f 0 =
        𝟙 _ ≫ Presheaf.OrderedCechEdge.augmentation V (K.X q)
      rw [Category.id_comp]
      exact augmentation_refinement U V r (K.X q))
  simpa only [Category.id_comp, Presheaf.OrderedCechEdge.edge,
    Refinement.totalMap] using h

theorem homology (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (q : ℕ) :
    homologyMap (Presheaf.OrderedCechEdge.edge U K) q ≫
      homologyMap (Refinement.totalMap U V r K) q =
        homologyMap (Presheaf.OrderedCechEdge.edge V K) q := by
  simpa only [homologyMap_comp] using congrArg (fun f => homologyMap f q) (edge U V r K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.EdgeRefinement
