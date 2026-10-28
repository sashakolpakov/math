import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnZeroCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge
import Mathlib.Algebra.Homology.Additive

/-! # Single Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleEdge

noncomputable section

/-! The original single-column total comparison takes the horizontal
edge to its coefficient augmentation, with coefficient one. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  (F : C ⥤ CochainComplex D ℕ) [F.Additive]
  (E : C ⥤ D) [E.Additive]
  (a : E ⟶ F ⋙ HomologicalComplex.eval D (.up ℕ) 0)
  (ha : ∀ M, a.app M ≫ (F.obj M).d 0 1 = 0)
  (M : C) (c : ℕ)

abbrev source := (E.mapHomologicalComplex (.up ℕ)).obj ((single C (.up ℕ) c).obj M)

def edge : source E M c ⟶ (SingleTotal.bicomplex F M c).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (SingleTotal.bicomplex F M c)) (source E M c)
    (fun q => a.app (((single C (.up ℕ) c).obj M).X q))
    (fun q q' _ => (a.naturality (((single C (.up ℕ) c).obj M).d q q')).symm)
    (fun _q => ha _)

def sourceIso : (source E M c).homology c ≅ E.obj M :=
  homologyMapIso ((singleMapHomologicalComplex E (.up ℕ) c).app M) c ≪≫
    singleObjHomologySelfIso (.up ℕ) c (E.obj M)

omit [HasCoproducts D] in
theorem source_coordinate :
    (source E M c).homologyπ c ≫ (sourceIso E M c).hom =
      (source E M c).iCycles c ≫ E.map (singleObjXSelf (.up ℕ) c M).hom := by
  let e : source E M c ≅ (single D (.up ℕ) c).obj (E.obj M) :=
    (singleMapHomologicalComplex E (.up ℕ) c).app M
  have hh := homologyπ_singleObjHomologySelfIso_hom (.up ℕ) c (E.obj M)
  change (source E M c).homologyπ c ≫ (homologyMap e.hom c ≫ _) = _
  rw [← Category.assoc, homologyπ_naturality, Category.assoc]
  calc
    _ = cyclesMap e.hom c ≫ (((single D (.up ℕ) c).obj (E.obj M)).iCycles c ≫
        (singleObjXSelf (.up ℕ) c (E.obj M)).hom) :=
      congrArg (cyclesMap e.hom c ≫ ·) hh
    _ = ((source E M c).iCycles c ≫ e.hom.f c) ≫
        (singleObjXSelf (.up ℕ) c (E.obj M)).hom := by
      simpa only [Category.assoc] using congrArg (· ≫ (singleObjXSelf (.up ℕ) c (E.obj M)).hom)
        (cyclesMap_i e.hom c)
    _ = _ := by
      have he : e.hom.f c = E.map (singleObjXSelf (.up ℕ) c M).hom ≫
          (singleObjXSelf (.up ℕ) c (E.obj M)).inv :=
        singleMapHomologicalComplex_hom_app_self E (.up ℕ) c M
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        congrArg (fun f => (source E M c).iCycles c ≫ f ≫
          (singleObjXSelf (.up ℕ) c (E.obj M)).hom) he

def columnIsoAt (j : ℕ) (hj : 0+c=j) :
    ((SingleTotal.bicomplex F M c).total (.up ℕ)).homology j ≅
      (F.obj M).homology 0 :=
  eqToIso (congrArg (fun q => ((SingleTotal.bicomplex F M c).total
    (.up ℕ)).homology q) hj.symm) ≪≫ SingleTotal.homologyIso F M c 0

theorem column_coordinateAt (j : ℕ) (hj : 0+c=j) :
    ((SingleTotal.bicomplex F M c).total (.up ℕ)).homologyπ j ≫
      (columnIsoAt F M c j hj).hom ≫ (CochainComplex.isoHomologyπ₀ (F.obj M)).inv ≫
        (F.obj M).iCycles 0 =
    ((SingleTotal.bicomplex F M c).total (.up ℕ)).iCycles j ≫
      AbelianSingleRowTotal.projection (SingleTotal.bicomplex F M c)
        c 0 j (by omega) ≫ (SingleTotal.rowIso F M c).hom.f 0 := by
  subst j
  simpa only [columnIsoAt, eqToIso_refl, Iso.refl_trans] using
    Single.ColumnZeroCoordinates.coordinate F M c

abbrev columnIso := columnIsoAt F M c c (Nat.zero_add c)
abbrev column_coordinate := column_coordinateAt F M c c (Nat.zero_add c)

theorem coordinate :
    (source E M c).homologyπ c ≫ homologyMap (edge F E a ha M c) c ≫
      (columnIso F M c).hom ≫
        (CochainComplex.isoHomologyπ₀ (F.obj M)).inv ≫ (F.obj M).iCycles 0 =
      (source E M c).iCycles c ≫ E.map (singleObjXSelf (.up ℕ) c M).hom ≫ a.app M := by
  have hc := column_coordinate F M c
  rw [← Category.assoc, homologyπ_naturality]
  simp only [Category.assoc]
  rw [hc, ← Category.assoc, cyclesMap_i]
  change ((source E M c).iCycles c ≫
    (a.app (((single C (.up ℕ) c).obj M).X c) ≫
      (SingleTotal.bicomplex F M c).ιTotal (.up ℕ) c 0 c rfl)) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  have hp : (SingleTotal.bicomplex F M c).ιTotal (.up ℕ) c 0 c rfl ≫
      AbelianSingleRowTotal.projection (SingleTotal.bicomplex F M c)
        c 0 c (by omega) = 𝟙 _ := by simp [AbelianSingleRowTotal.projection]
  rw [← Category.assoc _ _ ((SingleTotal.rowIso F M c).hom.f 0), hp,
    ]
  have hid := Category.id_comp ((SingleTotal.rowIso F M c).hom.f 0)
  exact (congrArg (fun z => (source E M c).iCycles c ≫
    a.app (((single C (.up ℕ) c).obj M).X c) ≫ z) hid).trans
      (congrArg ((source E M c).iCycles c ≫ ·)
        (a.naturality (singleObjXSelf (.up ℕ) c M).hom).symm)

def augmentation : E.obj M ⟶ (F.obj M).homology 0 :=
  (F.obj M).liftCycles (a.app M) 1 (by simp) (ha M) ≫ (F.obj M).homologyπ 0

theorem normalization :
    homologyMap (edge F E a ha M c) c ≫
      (columnIso F M c).hom =
    (sourceIso E M c).hom ≫ augmentation F E a ha M := by
  apply (cancel_epi ((source E M c).homologyπ c)).mp
  apply (cancel_mono (CochainComplex.isoHomologyπ₀ (F.obj M)).inv).mp
  apply (cancel_mono ((F.obj M).iCycles 0)).mp
  simp only [Category.assoc]
  rw [coordinate]
  simp only [augmentation, ← Category.assoc]
  rw [source_coordinate]
  simp only [Category.assoc]
  have hz : (F.obj M).homologyπ 0 ≫ (CochainComplex.isoHomologyπ₀ (F.obj M)).inv = 𝟙 _ :=
    (CochainComplex.isoHomologyπ₀ (F.obj M)).hom_inv_id
  rw [← Category.assoc _ _ ((F.obj M).iCycles 0), hz, Category.id_comp,
    HomologicalComplex.liftCycles_i]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleEdge
