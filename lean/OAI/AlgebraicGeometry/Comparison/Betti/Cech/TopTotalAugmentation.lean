import OAI.AlgebraicGeometry.Comparison.Betti.Cech.RowSectionsProduct
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.TopAugmentationPullback

/-! # Top Total Augmentation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.TopTotalAugmentation

noncomputable section

/-! The actual top-section complex maps to the Čech total by the original restriction augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)

def additiveTopGlobalComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((RowSectionsProduct.additiveOpenSectionsFunctor (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K

def additiveGlobalTopIso : FlasqueCechTotal.additiveGlobalComplex K ≅ additiveTopGlobalComplex K :=
  (NatIso.mapHomologicalComplex
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop)
      (.up ℕ)).app K

def topCechTotalAugmentation : additiveTopGlobalComplex K ⟶
    (FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).total (.up ℕ) :=
  (additiveGlobalTopIso K).inv ≫ FlasqueCechTotal.globalCechTotalAugmentation U K

theorem topCechTotalAugmentation_f (q : ℕ) :
    (topCechTotalAugmentation U K).f q = SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation U (K.X q) ≫
      (FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).ιTotal (.up ℕ) q 0 q rfl :=
  (Category.assoc _ _ _).symm

theorem topCechTotalAugmentation_quasiIso (hU : ⨆ i, U i = ⊤)
    (hK : ∀ q, TopCat.Sheaf.IsFlasque (K.X q)) : QuasiIso (topCechTotalAugmentation U K) :=
  quasiIso_comp (additiveGlobalTopIso K).inv (FlasqueCechTotal.globalCechTotalAugmentation U K)
    (hφ := quasiIso_of_isIso _) (hφ' := FlasqueCechTotal.globalCechTotalAugmentation_quasiIso U K hU hK)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.TopTotalAugmentation
