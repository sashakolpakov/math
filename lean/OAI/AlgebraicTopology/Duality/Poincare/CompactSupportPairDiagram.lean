import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportPairIndex
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-! # Compact Support Pair Diagram -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportPairDiagram

noncomputable section

/-!
# The compact-pair Mayer--Vietoris diagram

All four objects use actual relative singular cohomology. The first map
has signs `(+, +)` and the second map has signs `(+, -)`. Their colimit
maps are the corresponding extensions between ambient support colimits.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- The actual direct sum at every compact pair. -/
abbrev compactSupportPairMiddleDiagram (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :=
  (pointwiseBinaryBicone (CompactSupportPairIndex.compactSupportPairLeftDiagram M U V n)
    (CompactSupportPairIndex.compactSupportPairRightDiagram M U V n)).pt

/-- The pointwise direct-sum diagram is the categorical biproduct of the
two genuine support diagrams. -/
def compactSupportPairMiddleDiagramIso (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    compactSupportPairMiddleDiagram M U V n ≅
      CompactSupportPairIndex.compactSupportPairLeftDiagram M U V n ⊞ CompactSupportPairIndex.compactSupportPairRightDiagram M U V n :=
  biprod.uniqueUpToIso _ _ (pointwiseBinaryBicone.isBilimit _ _)

/-- The canonical colimit comparison for the direct sum. -/
def compactSupportPairMiddleColimitIso (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    colimit (compactSupportPairMiddleDiagram M U V n) ≅
      CompactSupportInsideMaps.compactSupportedInsideCohomology M U n ⊞ CompactSupportInsideMaps.compactSupportedInsideCohomology M V n := by
  let F := CompactSupportPairIndex.compactSupportPairLeftDiagram M U V n
  let G := CompactSupportPairIndex.compactSupportPairRightDiagram M U V n
  let C : ((U.compactsInside × V.compactsInside) ⥤ ModuleCat.{0} R) ⥤ ModuleCat.{0} R := colim
  letI : PreservesBinaryBiproduct F G C :=
    preservesBinaryBiproduct_of_preservesBiproduct C _ _
  exact C.mapIso (compactSupportPairMiddleDiagramIso M U V n) ≪≫ C.mapBiprod F G ≪≫
    biprod.mapIso (CompactSupportPairIndex.compactSupportPairLeftColimitIso M U V n)
      (CompactSupportPairIndex.compactSupportPairRightColimitIso M U V n)

@[reassoc (attr := simp)]
theorem compactSupportPairMiddleColimitIso_ι (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    colimit.ι (compactSupportPairMiddleDiagram M U V n) p ≫
        (compactSupportPairMiddleColimitIso M U V n).hom =
      biprod.map (colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M U n) p.1)
        (colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M V n) p.2) := by
  apply biprod.hom_ext
  · simp only [compactSupportPairMiddleColimitIso, Iso.trans_hom, Functor.mapIso_hom,
      biprod.mapIso_hom, Category.assoc, biprod.map_fst, Functor.mapBiprod_hom,
      biprod.lift_fst_assoc]
    rw [← Functor.map_comp_assoc]
    simp only [compactSupportPairMiddleDiagramIso, biprod.uniqueUpToIso_hom,
      biprod.lift_fst]
    erw [ι_colimMap_assoc]
    exact congrArg (fun f => biprod.fst ≫ f) (CompactSupportPairIndex.compactSupportPairLeftColimitIso_ι M U V n p)
  · simp only [compactSupportPairMiddleColimitIso, Iso.trans_hom, Functor.mapIso_hom,
      biprod.mapIso_hom, Category.assoc, biprod.map_snd, Functor.mapBiprod_hom,
      biprod.lift_snd_assoc]
    rw [← Functor.map_comp_assoc]
    simp only [compactSupportPairMiddleDiagramIso, biprod.uniqueUpToIso_hom,
      biprod.lift_snd]
    erw [ι_colimMap_assoc]
    exact congrArg (fun f => biprod.snd ≫ f) (CompactSupportPairIndex.compactSupportPairRightColimitIso_ι M U V n p)

/-- Enlargement from the intersection to each support, with signs `(+, +)`. -/
def compactSupportPairFirst [T2Space X] (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    CompactSupportPairIndex.compactSupportPairIntersectionDiagram M U V n ⟶ compactSupportPairMiddleDiagram M U V n where
  app p := biprod.lift (CompactSupportColimit.compactSupportCohomologyMap M
    (show p.1.val ⊓ p.2.val ≤ p.1.val from inf_le_left) n)
    (CompactSupportColimit.compactSupportCohomologyMap M
      (show p.1.val ⊓ p.2.val ≤ p.2.val from inf_le_right) n)
  naturality p q f := by
    change CompactSupportColimit.compactSupportCohomologyMap M
        (inf_le_inf (show p.1.val ≤ q.1.val from leOfHom f.1)
          (show p.2.val ≤ q.2.val from leOfHom f.2)) n ≫ biprod.lift _ _ =
      biprod.lift _ _ ≫ biprod.map
        (CompactSupportColimit.compactSupportCohomologyMap M (show p.1.val ≤ q.1.val from leOfHom f.1) n)
        (CompactSupportColimit.compactSupportCohomologyMap M (show p.2.val ≤ q.2.val from leOfHom f.2) n)
    apply biprod.hom_ext <;> simp [CompactSupportColimit.compactSupportCohomologyMap_comp]

/-- Enlargement to the union, with signs `(+, -)`. -/
def compactSupportPairSecond (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    compactSupportPairMiddleDiagram M U V n ⟶ CompactSupportPairIndex.compactSupportPairUnionDiagram M U V n where
  app p := biprod.desc (CompactSupportColimit.compactSupportCohomologyMap M
    (show p.1.val ≤ p.1.val ⊔ p.2.val from le_sup_left) n)
    (-CompactSupportColimit.compactSupportCohomologyMap M
      (show p.2.val ≤ p.1.val ⊔ p.2.val from le_sup_right) n)
  naturality p q f := by
    change biprod.map
        (CompactSupportColimit.compactSupportCohomologyMap M (show p.1.val ≤ q.1.val from leOfHom f.1) n)
        (CompactSupportColimit.compactSupportCohomologyMap M (show p.2.val ≤ q.2.val from leOfHom f.2) n) ≫
      biprod.desc _ _ = biprod.desc _ _ ≫ CompactSupportColimit.compactSupportCohomologyMap M
        (sup_le_sup (show p.1.val ≤ q.1.val from leOfHom f.1)
          (show p.2.val ≤ q.2.val from leOfHom f.2)) n
    apply biprod.hom_ext' <;> simp [CompactSupportColimit.compactSupportCohomologyMap_comp]

@[reassoc (attr := simp)]
theorem compactSupportPairFirst_second [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    compactSupportPairFirst M U V n ≫ compactSupportPairSecond M U V n = 0 := by
  apply NatTrans.ext
  funext p
  change biprod.lift _ _ ≫ biprod.desc _ _ = 0
  simp only [biprod.lift_desc, Preadditive.comp_neg, CompactSupportColimit.compactSupportCohomologyMap_comp,
    add_neg_cancel]

/-- Enlargement of a compact support does not change its class in the
colimit over the same open set. -/
@[reassoc (attr := simp)]
theorem compactSupportCohomologyMap_insideι (M : ModuleCat.{0} R) (U : Opens X) (n : ℕ)
    {K L : U.compactsInside} (h : K ≤ L) :
    CompactSupportColimit.compactSupportCohomologyMap M (show K.val ≤ L.val from h) n ≫
        colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M U n) L =
      colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M U n) K :=
  colimit.w (CompactSupportInsideMaps.compactSupportInsideDiagram M U n) (homOfLE h)

/-- Extension from the intersection to each open, with signs `(+, +)`. -/
def compactSupportInsideMayerVietorisFirst (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    CompactSupportInsideMaps.compactSupportedInsideCohomology M (U ⊓ V) n ⟶
      CompactSupportInsideMaps.compactSupportedInsideCohomology M U n ⊞ CompactSupportInsideMaps.compactSupportedInsideCohomology M V n :=
  biprod.lift (CompactSupportInsideMaps.compactSupportInsideMap M (show U ⊓ V ≤ U from inf_le_left) n)
    (CompactSupportInsideMaps.compactSupportInsideMap M (show U ⊓ V ≤ V from inf_le_right) n)

/-- The difference of extension from the two opens to their union. -/
def compactSupportInsideMayerVietorisSecond (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    CompactSupportInsideMaps.compactSupportedInsideCohomology M U n ⊞ CompactSupportInsideMaps.compactSupportedInsideCohomology M V n ⟶
      CompactSupportInsideMaps.compactSupportedInsideCohomology M (U ⊔ V) n :=
  biprod.desc (CompactSupportInsideMaps.compactSupportInsideMap M (show U ≤ U ⊔ V from le_sup_left) n)
    (-CompactSupportInsideMaps.compactSupportInsideMap M (show V ≤ U ⊔ V from le_sup_right) n)

@[reassoc (attr := simp)]
theorem compactSupportInsideMayerVietorisFirst_second
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    compactSupportInsideMayerVietorisFirst M U V n ≫
      compactSupportInsideMayerVietorisSecond M U V n = 0 := by
  simp only [compactSupportInsideMayerVietorisFirst, compactSupportInsideMayerVietorisSecond,
    biprod.lift_desc, Preadditive.comp_neg, CompactSupportInsideMaps.compactSupportInsideMap_comp, add_neg_cancel]

/-- The first map obtained from compact pairs is exactly extension to the
two opens, with the specified signs. -/
@[reassoc]
theorem compactSupportPairFirst_colimit [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    colimMap (compactSupportPairFirst M U V n) ≫
        (compactSupportPairMiddleColimitIso M U V n).hom =
      (CompactSupportPairIndex.compactSupportPairIntersectionColimitIso M U V n).hom ≫
        compactSupportInsideMayerVietorisFirst M U V n := by
  apply colimit.hom_ext
  intro p
  simp only [ι_colimMap_assoc,
    compactSupportPairMiddleColimitIso_ι,
    CompactSupportPairIndex.compactSupportPairIntersectionColimitIso_ι_assoc]
  apply biprod.hom_ext
  · simp only [compactSupportPairFirst, compactSupportInsideMayerVietorisFirst,
      Category.assoc, biprod.map_fst, biprod.lift_fst,
      CompactSupportInsideMaps.compactSupportInsideMap_ι]
    erw [biprod.lift_fst_assoc]
    exact compactSupportCohomologyMap_insideι M U n
      (K := (CompactSupportInsideMaps.compactsInsideMap (show U ⊓ V ≤ U from inf_le_left)).obj
        (CompactSupportPairIndex.compactPairIntersection U V p)) (L := p.1) (show p.1.val ⊓ p.2.val ≤ p.1.val from inf_le_left)
  · simp only [compactSupportPairFirst, compactSupportInsideMayerVietorisFirst,
      Category.assoc, biprod.map_snd, biprod.lift_snd,
      CompactSupportInsideMaps.compactSupportInsideMap_ι]
    erw [biprod.lift_snd_assoc]
    exact compactSupportCohomologyMap_insideι M V n
      (K := (CompactSupportInsideMaps.compactsInsideMap (show U ⊓ V ≤ V from inf_le_right)).obj
        (CompactSupportPairIndex.compactPairIntersection U V p)) (L := p.2) (show p.1.val ⊓ p.2.val ≤ p.2.val from inf_le_right)

/-- The second compact-pair map is exactly the difference of open extensions. -/
@[reassoc]
theorem compactSupportPairSecond_colimit [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    colimMap (compactSupportPairSecond M U V n) ≫
        (CompactSupportPairIndex.compactSupportPairUnionColimitIso M U V n).hom =
      (compactSupportPairMiddleColimitIso M U V n).hom ≫
        compactSupportInsideMayerVietorisSecond M U V n := by
  apply colimit.hom_ext
  intro p
  simp only [ι_colimMap_assoc,
    CompactSupportPairIndex.compactSupportPairUnionColimitIso_ι,
    compactSupportPairMiddleColimitIso_ι_assoc]
  apply biprod.hom_ext'
  · simp only [compactSupportPairSecond, compactSupportInsideMayerVietorisSecond,
      biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc,
      CompactSupportInsideMaps.compactSupportInsideMap_ι]
    exact compactSupportCohomologyMap_insideι M (U ⊔ V) n
      (K := (CompactSupportInsideMaps.compactsInsideMap (show U ≤ U ⊔ V from le_sup_left)).obj p.1)
      (L := CompactSupportDecomposition.compactPairUnion U V p) (show p.1.val ≤ p.1.val ⊔ p.2.val from le_sup_left)
  · simp only [compactSupportPairSecond, compactSupportInsideMayerVietorisSecond,
      biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
      Preadditive.neg_comp, Preadditive.comp_neg, CompactSupportInsideMaps.compactSupportInsideMap_ι]
    exact congrArg Neg.neg (compactSupportCohomologyMap_insideι M (U ⊔ V) n
      (K := (CompactSupportInsideMaps.compactsInsideMap (show V ≤ U ⊔ V from le_sup_right)).obj p.2)
      (L := CompactSupportDecomposition.compactPairUnion U V p) (show p.2.val ≤ p.1.val ⊔ p.2.val from le_sup_right))

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportPairDiagram
