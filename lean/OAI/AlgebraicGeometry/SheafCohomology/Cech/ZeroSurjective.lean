import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZero

/-! # Zero Surjective -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.ZeroSurjective.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! An open cover computes degree-zero cohomology by gluing global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

theorem cechGlobalSectionsToHZero_surjective (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) : Function.Surjective (DegreeZero.TopCat.Sheaf.cechGlobalSectionsToHZero U F) := by
  let K := (cechComplexFunctor U).obj F.obj
  let a := GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U
  let l := K.liftCycles a 1 (by simp) (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d F U)
  intro x
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ 0)).mp inferInstance x
  have hcycle : K.d 0 1 (K.iCycles 0 z) = 0 :=
    ConcreteCategory.congr_hom (K.iCycles_d 0 1) z
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp
    (InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U F hU) (K.iCycles 0 z) hcycle
  have hLift : l y = z := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
    have hl : l ≫ K.iCycles 0 = a := K.liftCycles_i _ _ _ _
    exact (ConcreteCategory.congr_hom hl y).trans hy
  refine ⟨y, ?_⟩
  change K.homologyπ 0 (l y) = x
  rw [hLift, hz]

theorem cechTopSectionsToHZero_surjective (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) : Function.Surjective (TopZero.TopCat.Sheaf.cechTopSectionsToHZero U F) :=
  (cechGlobalSectionsToHZero_surjective U F hU).comp
    (((CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app F).symm.addCommGroupIsoToAddEquiv.surjective)

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.ZeroSurjective.TopCat.Sheaf
