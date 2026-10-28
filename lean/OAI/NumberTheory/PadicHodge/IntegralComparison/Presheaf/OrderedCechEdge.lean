import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.GlobalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

/-! # Ordered Cech Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge

noncomputable section

/-! The usual global-section edge for the original ordered Čech complex,
with arbitrary additive presheaf coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : (Opens X)ᵒᵖ ⥤ D)

abbrev augmentation := RelativeCech.GlobalSections.globalAugmentation V P

omit [Preadditive D] in
theorem augmentation_projection (a : AugmentedOrdered.Cech.Index ι 1) :
    augmentation V P ≫ Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 => P.obj (op ((AugmentedOrdered.Cech.formal V 1).obj b))) a =
      P.map (homOfLE (le_top : (AugmentedOrdered.Cech.formal V 1).obj a ≤ ⊤)).op := Pi.lift_comp_π _ a

omit [Preadditive D] in
theorem coface_coordinate (a : AugmentedOrdered.Cech.Index ι 2) (j : Fin 2) :
    (augmentation V P ≫ AugmentedOrdered.Cech.coface V P 1 j) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι 2 => P.obj (op ((AugmentedOrdered.Cech.formal V 2).obj b))) a =
        P.map (homOfLE (le_top : (AugmentedOrdered.Cech.formal V 2).obj a ≤ ⊤)).op := by
  rw [Category.assoc, AugmentedOrdered.CechCoordinates.coface_comp_pi, ← Category.assoc, augmentation_projection, ← P.map_comp]
  congr 1

theorem augmentation_d : augmentation V P ≫ AugmentedOrdered.Cech.differential V P 1 = 0 := by
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index ι 2)
  rw [zero_comp]
  change (augmentation V P ≫ AugmentedOrdered.Cech.differential V P 1) ≫
    Pi.π (fun b : AugmentedOrdered.Cech.Index ι 2 => P.obj (op ((AugmentedOrdered.Cech.formal V 2).obj b))) a = 0
  simp only [AugmentedOrdered.Cech.differential, Nat.reduceAdd, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_zsmul, neg_one_zsmul, comp_add, add_comp, comp_neg,
    neg_comp, coface_coordinate, add_neg_cancel]

omit [Preadditive D] in
theorem augmentation_naturality {Q : (Opens X)ᵒᵖ ⥤ D} (f : P ⟶ Q) :
    f.app (op (⊤ : Opens X)) ≫ augmentation V Q =
      augmentation V P ≫ AugmentedOrdered.CechFunctor.objectMap V f 1 := by
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index ι 1)
  change (f.app (op (⊤ : Opens X)) ≫ augmentation V Q) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 => Q.obj (op ((AugmentedOrdered.Cech.formal V 1).obj b))) a =
    (augmentation V P ≫ AugmentedOrdered.CechFunctor.objectMap V f 1) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 => Q.obj (op ((AugmentedOrdered.Cech.formal V 1).obj b))) a
  rw [Category.assoc, augmentation_projection, Category.assoc,
    AugmentedOrdered.CechCoordinates.objectMap_comp_pi, ← Category.assoc, augmentation_projection]
  exact (f.naturality _).symm

def bicomplex (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) :
    HomologicalComplex₂ D (.up ℕ) (.up ℕ) :=
  ((OrderedCech.Functor.Projection.functor V).mapHomologicalComplex (.up ℕ)).obj K

def sections (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) : CochainComplex D ℕ :=
  (((evaluation (Opens X)ᵒᵖ D).obj (op (⊤ : Opens X))).mapHomologicalComplex (.up ℕ)).obj K

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)

theorem augmentation_comm (q q' : ℕ) :
    augmentation V (K.X q) ≫ ((OrderedCechEdge.bicomplex V K).d q q').f 0 =
      (sections K).d q q' ≫ augmentation V (K.X q') :=
  (augmentation_naturality V (K.X q) (K.d q q')).symm

theorem augmentation_cocycle (q : ℕ) :
    augmentation V (K.X q) ≫ ((OrderedCechEdge.bicomplex V K).X q).d 0 1 = 0 := by
  change augmentation V (K.X q) ≫ (OrderedCech.Projection.complex V (K.X q)).d 0 1 = 0
  have hd : (OrderedCech.Projection.complex V (K.X q)).d 0 1 = AugmentedOrdered.Cech.differential V (K.X q) 1 :=
    CochainComplex.of_d (OrderedCech.Projection.object V (K.X q))
      (OrderedCech.Projection.differential V (K.X q)) 0
  rw [hd]
  exact augmentation_d V (K.X q)

variable [HasCoproducts.{0} D]

def edge : sections K ⟶ (OrderedCechEdge.bicomplex V K).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex V K)) (sections K)
    (fun q => augmentation V (K.X q)) (fun q q' _ => augmentation_comm V K q q')
    (augmentation_cocycle V K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge
