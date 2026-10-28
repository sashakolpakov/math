import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveVerticalEdge
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.HomologyComparison

/-! # Resolution Horizontal Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionHorizontalComparison.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (F := TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X)

/-- The horizontal edge from global sections of the injective resolution to
the total injective Cech bicomplex. -/
noncomputable def cechResolutionHorizontalEdge
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ResolutionSections.IntrinsicCech.cechResolutionSectionsComplex F ⟶
      (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).total (.up ℕ) :=
  TotalComplex.HorizontalEdge.totalUpNatHorizontalEdge (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F)
    (ResolutionSections.IntrinsicCech.cechResolutionSectionsComplex F)
    (ResolutionSections.IntrinsicCech.cechResolutionHorizontalAugmentation U F)
    (ResolutionSections.IntrinsicCech.cechResolutionHorizontalAugmentation_comm U F)
    (ResolutionSections.IntrinsicCech.cechResolutionHorizontalAugmentation_comp_d U F)

@[simp]
theorem cechResolutionHorizontalEdge_f
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    (cechResolutionHorizontalEdge U F).f q =
      ResolutionSections.IntrinsicCech.cechResolutionHorizontalAugmentation U F q ≫
        (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).ιTotal
          (.up ℕ) q 0 q rfl := by
  apply TotalComplex.HorizontalEdge.totalUpNatHorizontalEdge_f

theorem cechResolutionHorizontalEdge_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    (phi : InjectiveResolution.Hom
      (injectiveResolution F)
      (injectiveResolution G) f) :
    ResolutionSections.IntrinsicCech.cechResolutionSectionsMap phi.hom ≫
        cechResolutionHorizontalEdge U G =
      cechResolutionHorizontalEdge U F ≫
        InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionTotalMap U phi.hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  have hAug :
      ResolutionSections.IntrinsicCech.cechResolutionHorizontalAugmentation U F q ≫
          ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplexMap U phi.hom).f q).f 0 =
          (ResolutionSections.IntrinsicCech.cechResolutionSectionsMap phi.hom).f q ≫
          ResolutionSections.IntrinsicCech.cechResolutionHorizontalAugmentation U G q := by
    exact GlobalAugmentationNaturality.IntrinsicCech.cechGlobalSectionsAugmentation_naturality
      (U := U) (f := phi.hom.f q)
  simp only [HomologicalComplex.comp_f,
    cechResolutionHorizontalEdge_f]
  rw [Category.assoc, InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionTotalMap,
    HomologicalComplex₂.ιTotal_map]
  simp only [← Category.assoc]
  rw [hAug]

/-- Every row of the injective-resolution Čech bicomplex is exact in every positive degree. -/
theorem cechInjectiveResolution_rowsExact (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hU : ⨆ i, U i = ⊤) :
    TotalComplex.CycleNormalization.RowsExact (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F) := by
  intro q p
  let I := injectiveResolution F
  have : TopCat.Sheaf.IsFlasque (I.cocomplex.X q) :=
    @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X (I.cocomplex.X q) (I.injective q)
  apply (HomologicalComplex.exactAt_iff'
    ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).X q)
      p (p + 1) (p + 2) (by simp) (by simp)).1
  exact FlasqueIntrinsicCechExactness.IntrinsicCech.cechComplex_exactAt_succ_of_isFlasque (I.cocomplex.X q) U hU p

/-- The actual horizontal edge is a quasi-isomorphism in every positive degree. -/
theorem cechResolutionHorizontalEdge_quasiIsoAt_succ
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    QuasiIsoAt (cechResolutionHorizontalEdge U F) (n + 1) := by
  let I := injectiveResolution F
  apply TotalComplex.HomologyComparison.horizontal_edge_quasiIsoAt
  · intro q
    exact GlobalAugmentationExactness.IntrinsicCech.cechGlobalSectionsNativeShortComplex_exact U (I.cocomplex.X q) hU
  · intro q
    exact GlobalAugmentationExactness.IntrinsicCech.cechGlobalSectionsAugmentation_mono U (I.cocomplex.X q) hU
  · exact cechInjectiveResolution_rowsExact U F hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionHorizontalComparison.IntrinsicCech
