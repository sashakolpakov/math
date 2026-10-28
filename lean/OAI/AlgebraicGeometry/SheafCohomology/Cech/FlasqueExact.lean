/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechAcyclicComparison.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueResolution
import OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSections
import OAI.AlgebraicGeometry.SheafCohomology.Cech.DerivedGlobalSections

/-! # Flasque Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueExact.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! Positive-degree exactness of the native Čech complex of a flasque sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable local instance e35FlasqueSections_additive : (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

private abbrev cechSiteDifferential (n : ℕ) :
    Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U n) ⟶ Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U (n + 1)) :=
  SheafDifferential.TopCat.Sheaf.cechDifferential F U n

private theorem cechGlobalSections_exactAt_succ [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
      (SheafComplex.TopCat.Sheaf.cechComplex F U)).ExactAt (n + 1) := by
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk
      ((globalSections X).map (cechSiteDifferential F U n))
      ((globalSections X).map (cechSiteDifferential F U (n + 1))) (by
        calc
          _ = (globalSections X).map
              (cechSiteDifferential F U n ≫ cechSiteDifferential F U (n + 1)) :=
            ((globalSections X).map_comp _ _).symm
          _ = (globalSections X).map 0 :=
            congrArg (globalSections X).map (SheafComplex.TopCat.Sheaf.cechDifferential_comp F U n)
          _ = 0 := (globalSections X).map_zero
            (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U n)) (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U (n + 2))))
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
    let xTop := eΓ.hom.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U (n + 1))) x
    have hxTop : (SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op ⊤) xTop = 0 := by
      calc
        _ = eΓ.hom.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U (n + 2)))
            ((globalSections X).map (cechSiteDifferential F U (n + 1)) x) :=
          (ConcreteCategory.congr_hom
            (eΓ.hom.naturality (cechSiteDifferential F U (n + 1))) x).symm
        _ = 0 := by rw [hx, map_zero]
    obtain ⟨yTop, hyTop⟩ := FlasqueResolution.TopCat.Sheaf.cechSections_exact_succ F U hU n ⊤ xTop hxTop
    let y := eΓ.inv.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U n)) yTop
    have hyInv : eΓ.hom.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U n)) y = yTop := by
      exact Iso.inv_hom_id_apply (eΓ.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U n))) yTop
    have hyTop' :
        (SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op (⊤ : Opens X)) yTop = xTop := by
      exact hyTop
    refine ⟨y, ?_⟩
    change (globalSections X).map (cechSiteDifferential F U n) y = x
    apply (AddCommGrpCat.mono_iff_injective
      (eΓ.hom.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U (n + 1))))).mp inferInstance
    have hnat :
        eΓ.hom.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U (n + 1)))
            ((globalSections X).map (cechSiteDifferential F U n) y) =
          (SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op (⊤ : Opens X))
            (eΓ.hom.app (Compat.TopCat.Sheaf.toSiteSheaf (Terms.TopCat.Sheaf.cechTerm F U n)) y) :=
      ConcreteCategory.congr_hom
        (eΓ.hom.naturality (cechSiteDifferential F U n)) y
    refine hnat.trans ?_
    rw [hyInv]
    exact hyTop'
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk
    ((globalSections X).map ((SheafComplex.TopCat.Sheaf.cechComplex F U).d n (n + 1)))
    ((globalSections X).map ((SheafComplex.TopCat.Sheaf.cechComplex F U).d (n + 1) (n + 2))) _).Exact
  simp only [SheafComplex.TopCat.Sheaf.cechComplex_d]
  exact hS

/-- The native Cech complex of a flasque sheaf is exact in every positive degree. -/
theorem cechComplex_exactAt_succ_of_isFlasque [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) :=
  (cechGlobalSections_exactAt_succ F U hU n).of_iso
    (GlobalSections.TopCat.Sheaf.cechGlobalSectionsComplexIso F U)

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueExact.TopCat.Sheaf
