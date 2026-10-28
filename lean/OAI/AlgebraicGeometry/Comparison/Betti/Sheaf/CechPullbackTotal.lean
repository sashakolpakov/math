import OAI.AlgebraicGeometry.Comparison.Betti.Cech.TopTotalAugmentation
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex

/-! # Cech Pullback Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal

noncomputable section

/-! Actual coefficient pullback commutes with the top-section augmentation into Čech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex₂

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)

local instance cechAdditivePushforward : (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

def additivePresheafComplexOfSheaves
    {Z : TopCat.{0}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Z) ℕ) :
    CochainComplex ((Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  ((TopCat.Sheaf.forget AddCommGrpCat.{0} Z).mapHomologicalComplex (.up ℕ)).obj K

variable {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ}
  (α : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj L)

def additiveDirectImagePresheafMap : additivePresheafComplexOfSheaves K ⟶
    ((AdditiveCechPullbackBicomplex.additivePresheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj (additivePresheafComplexOfSheaves L) :=
  ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).mapHomologicalComplex (.up ℕ)).map α

def sheafCechPullbackBicomplexMap : FlasqueCechTotal.additiveSheafSectionCechBicomplex U K ⟶
    FlasqueCechTotal.additiveSheafSectionCechBicomplex (fun i => (Opens.map f).obj (U i)) L :=
  AdditiveCechPullbackBicomplex.additiveCechPullbackBicomplexMap f U (additiveDirectImagePresheafMap f α)

def topGlobalSectionsPullback : Cech.TopTotalAugmentation.additiveTopGlobalComplex K ⟶ Cech.TopTotalAugmentation.additiveTopGlobalComplex L where
  f q := (α.f q).hom.app (op ⊤)
  comm' q q' _ := congrArg (fun g => g.hom.app (op (⊤ : Opens X))) (α.comm q q')

def sheafCechPullbackTotalMap : (FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).total (.up ℕ) ⟶
    (FlasqueCechTotal.additiveSheafSectionCechBicomplex (fun i => (Opens.map f).obj (U i)) L).total (.up ℕ) :=
  total.map (sheafCechPullbackBicomplexMap f U α) (.up ℕ)

theorem sheafCechPullbackTotalMap_topAugmentation
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤) :
    Cech.TopTotalAugmentation.topCechTotalAugmentation U K ≫ sheafCechPullbackTotalMap f U α =
      topGlobalSectionsPullback f α ≫ Cech.TopTotalAugmentation.topCechTotalAugmentation (fun i => (Opens.map f).obj (U i)) L := by
  apply HomologicalComplex.Hom.ext
  funext q
  let B := FlasqueCechTotal.additiveSheafSectionCechBicomplex U K
  let C := FlasqueCechTotal.additiveSheafSectionCechBicomplex (fun i => (Opens.map f).obj (U i)) L
  let φ : B ⟶ C := sheafCechPullbackBicomplexMap f U α
  have hu : SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation U (K.X q) ≫ (φ.f q).f 0 =
      (α.f q).hom.app (op ⊤) ≫
        SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation (fun i => (Opens.map f).obj (U i)) (L.X q) :=
    Cech.TopAugmentationPullback.additiveCechPullback_topAugmentation f U (K.X q) (L.X q) (α.f q).hom hU hV
  change (Cech.TopTotalAugmentation.topCechTotalAugmentation U K).f q ≫ (total.map φ (.up ℕ)).f q =
    (α.f q).hom.app (op ⊤) ≫ (Cech.TopTotalAugmentation.topCechTotalAugmentation (fun i => (Opens.map f).obj (U i)) L).f q
  rw [Cech.TopTotalAugmentation.topCechTotalAugmentation_f, Cech.TopTotalAugmentation.topCechTotalAugmentation_f]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation U (K.X q) ≫ a)
      (ιTotal_map B C φ (.up ℕ) q 0 q rfl)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ C.ιTotal (.up ℕ) q 0 q rfl) hu).trans (Category.assoc _ _ _))))

theorem topGlobalSectionsPullback_quasiIso_of_flasque
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤)
    (hK : ∀ q, TopCat.Sheaf.IsFlasque (K.X q)) (hL : ∀ q, TopCat.Sheaf.IsFlasque (L.X q))
    (hα : QuasiIso (sheafCechPullbackTotalMap f U α)) : QuasiIso (topGlobalSectionsPullback f α) := by
  have heK : QuasiIso (Cech.TopTotalAugmentation.topCechTotalAugmentation U K) := Cech.TopTotalAugmentation.topCechTotalAugmentation_quasiIso U K hU hK
  have heL : QuasiIso (Cech.TopTotalAugmentation.topCechTotalAugmentation (fun i => (Opens.map f).obj (U i)) L) :=
    Cech.TopTotalAugmentation.topCechTotalAugmentation_quasiIso _ L hV hL
  have hc : QuasiIso (topGlobalSectionsPullback f α ≫
      Cech.TopTotalAugmentation.topCechTotalAugmentation (fun i => (Opens.map f).obj (U i)) L) := by
    rw [← sheafCechPullbackTotalMap_topAugmentation f U α hU hV]
    exact quasiIso_comp _ _ (hφ := heK) (hφ' := hα)
  exact quasiIso_of_comp_right _ _ (hφ := heL) (hφφ' := hc)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal
