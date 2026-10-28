/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechAcyclicComparison.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueCechSectionExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafCohomology

/-! # Flasque Intrinsic Cech Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueIntrinsicCechExactness.IntrinsicCech

noncomputable section

/-! Positive-degree exactness of the native Čech complex of a flasque sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable local instance flasqueSections_additive : (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

abbrev cechSiteDifferential (n : ℕ) :
    TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U n) ⟶ TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)) :=
  Cech.SheafDifferential.IntrinsicCech.cechDifferential F U n

theorem cechGlobalSections_exactAt_succ [TopCat.Sheaf.IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
      (IntrinsicCech.SheafComplex.cechComplex F U)).ExactAt (n + 1) := by
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk
      ((globalSections X).map (cechSiteDifferential F U n))
      ((globalSections X).map (cechSiteDifferential F U (n + 1))) (by
        calc
          _ = (globalSections X).map
              (cechSiteDifferential F U n ≫ cechSiteDifferential F U (n + 1)) :=
            ((globalSections X).map_comp _ _).symm
          _ = (globalSections X).map 0 :=
            congrArg (globalSections X).map (IntrinsicCech.SheafComplex.cechDifferential_comp F U n)
          _ = 0 := (globalSections X).map_zero
            (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U n)) (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U (n + 2))))
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
    let xTop := eΓ.hom.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U (n + 1))) x
    have hxTop : (Cech.SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op ⊤) xTop = 0 := by
      calc
        _ = eΓ.hom.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)))
            ((globalSections X).map (cechSiteDifferential F U (n + 1)) x) :=
          (ConcreteCategory.congr_hom
            (eΓ.hom.naturality (cechSiteDifferential F U (n + 1))) x).symm
        _ = 0 := by rw [hx, map_zero]
    obtain ⟨yTop, hyTop⟩ := FlasqueCechSectionExactness.IntrinsicCech.cechSections_exact_succ F U hU n ⊤ xTop hxTop
    let y := eΓ.inv.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U n)) yTop
    have hyInv : eΓ.hom.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U n)) y = yTop := by
      exact Iso.inv_hom_id_apply (eΓ.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U n))) yTop
    have hyTop' :
        (Cech.SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op (⊤ : Opens X)) yTop = xTop := by
      exact hyTop
    refine ⟨y, ?_⟩
    change (globalSections X).map (cechSiteDifferential F U n) y = x
    apply (AddCommGrpCat.mono_iff_injective
      (eΓ.hom.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U (n + 1))))).mp inferInstance
    have hnat :
        eΓ.hom.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)))
            ((globalSections X).map (cechSiteDifferential F U n) y) =
          (Cech.SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op (⊤ : Opens X))
            (eΓ.hom.app (TopologicalSheafCohomology.IntrinsicCech.toSiteSheaf (IntrinsicCech.SheafTerms.cechTerm F U n)) y) :=
      ConcreteCategory.congr_hom
        (eΓ.hom.naturality (cechSiteDifferential F U n)) y
    refine hnat.trans ?_
    rw [hyInv]
    exact hyTop'
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk
    ((globalSections X).map ((IntrinsicCech.SheafComplex.cechComplex F U).d n (n + 1)))
    ((globalSections X).map ((IntrinsicCech.SheafComplex.cechComplex F U).d (n + 1) (n + 2))) _).Exact
  simp only [IntrinsicCech.SheafComplex.cechComplex_d]
  exact hS

/-- The native Cech complex of a flasque sheaf is exact in every positive degree. -/
theorem cechComplex_exactAt_succ_of_isFlasque [TopCat.Sheaf.IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) :=
  (cechGlobalSections_exactAt_succ F U hU n).of_iso
    (Cech.GlobalSectionsComplex.IntrinsicCech.cechGlobalSectionsComplexIso F U)

/-- The degree-one specialization of positive flasque Čech exactness. -/
theorem cechComplex_exactAt_one_of_isFlasque [TopCat.Sheaf.IsFlasque F]
    (hU : ⨆ i, U i = ⊤) :
    ((cechComplexFunctor U).obj F.obj).ExactAt 1 :=
  cechComplex_exactAt_succ_of_isFlasque F U hU 0

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueIntrinsicCechExactness.IntrinsicCech
