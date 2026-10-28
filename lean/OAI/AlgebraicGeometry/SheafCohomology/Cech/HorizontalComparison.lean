import OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueExact
import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveComparison
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison

/-! # Horizontal Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.HorizontalComparison.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! All positive horizontal comparisons for the actual Čech-injective double complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

noncomputable local instance e35HorizontalSections_additive : (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

noncomputable local instance e35HorizontalSections_preservesZero :
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (F := GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X)

/-- Global sections applied degreewise to the chosen injective resolution. -/
noncomputable def cechResolutionSectionsComplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
    (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex

noncomputable def cechResolutionSectionsMap
    {F G : Sheaf AddCommGrpCat.{u} X}
    (phi : (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex ⟶
      (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf G)).cocomplex) :
    cechResolutionSectionsComplex F ⟶
      cechResolutionSectionsComplex G :=
  ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map phi

@[simp]
theorem cechResolutionSectionsMap_f
    {F G : Sheaf AddCommGrpCat.{u} X}
    (phi : (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex ⟶
      (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf G)).cocomplex) (q : ℕ) :
    (cechResolutionSectionsMap phi).f q =
      (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (phi.f q) :=
  rfl

/-- The row augmentation from global sections of the resolution to native
Cech degree zero. -/
noncomputable def cechResolutionHorizontalAugmentation
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    (cechResolutionSectionsComplex F).X q ⟶
      ((InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).X q).X 0 :=
  GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation
    ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex.X q) U

@[simp]
theorem cechResolutionHorizontalAugmentation_eq
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    cechResolutionHorizontalAugmentation U F q =
      GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation
        ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex.X q) U :=
  rfl

theorem cechResolutionHorizontalAugmentation_comm
    (F : Sheaf AddCommGrpCat.{u} X) (q q' : ℕ)
    (_ : (ComplexShape.up ℕ).Rel q q') :
    cechResolutionHorizontalAugmentation U F q ≫
        ((InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).d q q').f 0 =
      (cechResolutionSectionsComplex F).d q q' ≫
        cechResolutionHorizontalAugmentation U F q' := by
  let I := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  change GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (I.cocomplex.X q) U ≫
      ((cechComplexFunctor U).map (I.cocomplex.d q q').hom).f 0 =
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (I.cocomplex.d q q') ≫
      GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (I.cocomplex.X q') U
  exact GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_naturality
    (U := U) (F := I.cocomplex.X q) (I.cocomplex.d q q')

theorem cechResolutionHorizontalAugmentation_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    cechResolutionHorizontalAugmentation U F q ≫
      ((InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).X q).d 0 1 = 0 := by
  let I := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  change GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (I.cocomplex.X q) U ≫
    ((cechComplexFunctor U).obj (I.cocomplex.X q).obj).d 0 1 = 0
  exact GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d (I.cocomplex.X q) U

/-- The horizontal edge from global sections of the injective resolution to
the total injective Cech bicomplex. -/
noncomputable def cechResolutionHorizontalEdge
    (F : Sheaf AddCommGrpCat.{u} X) :
    cechResolutionSectionsComplex F ⟶
      (InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).total (.up ℕ) :=
  (UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge
    (InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F))
    (cechResolutionSectionsComplex F)
    (cechResolutionHorizontalAugmentation U F)
    (cechResolutionHorizontalAugmentation_comm U F)
    (cechResolutionHorizontalAugmentation_comp_d U F)

@[simp]
theorem cechResolutionHorizontalEdge_f
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    (cechResolutionHorizontalEdge U F).f q =
      cechResolutionHorizontalAugmentation U F q ≫
        (InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).ιTotal
          (.up ℕ) q 0 q rfl := by
  rfl

theorem cechResolutionHorizontalEdge_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (phi : InjectiveResolution.Hom
      (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F))
      (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf G)) f) :
    cechResolutionSectionsMap phi.hom ≫
        cechResolutionHorizontalEdge U G =
      cechResolutionHorizontalEdge U F ≫
        InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionTotalMap U phi.hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  have hAug :
      cechResolutionHorizontalAugmentation U F q ≫
          ((InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplexMap U phi.hom).f q).f 0 =
          (cechResolutionSectionsMap phi.hom).f q ≫
          cechResolutionHorizontalAugmentation U G q := by
    rw [InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplexMap_f_f,
      cechResolutionSectionsMap_f,
      cechResolutionHorizontalAugmentation_eq,
      cechResolutionHorizontalAugmentation_eq]
    exact GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_naturality
      (U := U) (f := phi.hom.f q)
  simp only [HomologicalComplex.comp_f,
    cechResolutionHorizontalEdge_f]
  rw [Category.assoc, InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionTotalMap,
    HomologicalComplex₂.ιTotal_map]
  simp only [← Category.assoc]
  rw [hAug]

/-- Every row of the injective-resolution Čech bicomplex is exact in every positive degree. -/
theorem cechInjectiveResolution_rowsExact (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) :
    ComplexUpNatNormalize.Projective.RowsExact (InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F) := by
  intro q p
  let I := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  have : IsFlasque (I.cocomplex.X q) :=
    @Compat.TopCat.Sheaf.IsFlasque.of_injective X (I.cocomplex.X q) (I.injective q)
  apply (HomologicalComplex.exactAt_iff'
    ((InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).X q)
      p (p + 1) (p + 2) (by simp) (by simp)).1
  exact FlasqueExact.TopCat.Sheaf.cechComplex_exactAt_succ_of_isFlasque (I.cocomplex.X q) U hU p

/-- The actual horizontal edge is a quasi-isomorphism in every positive degree. -/
theorem cechResolutionHorizontalEdge_quasiIsoAt_succ
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    QuasiIsoAt (cechResolutionHorizontalEdge U F) (n + 1) := by
  let I := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  apply ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt
  · intro q
    exact InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U (I.cocomplex.X q) hU
  · intro q
    exact InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U (I.cocomplex.X q) hU
  · exact cechInjectiveResolution_rowsExact U F hU

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.HorizontalComparison.TopCat.Sheaf
