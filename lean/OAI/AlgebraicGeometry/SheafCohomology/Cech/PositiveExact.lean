/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafPositiveExact.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Cech.LocalContraction
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ZeroExact

/-! # Positive Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveExact.TopCat.Sheaf

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Positive-degree exactness of the sheaf-level Cech complex

This file applies the local Cech contraction to stalk representatives. When the chosen
opens cover the whole space, every positive-degree stalk cycle can be represented by a
cycle on a neighborhood contained in one cover member, where the local contraction gives
a preimage.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private theorem exists_cechCycle_restriction (hU : ⨆ i, U i = ⊤) (n : ℕ) (x : X)
    {V : Opens X} (hxV : x ∈ V)
    (s : (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).obj.obj (op V))
    (hy : (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).presheaf.germ V x hxV
      ((SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op V) s) = 0) :
    ∃ (i₀ : ι) (W : Opens X) (hxW : x ∈ W), W ≤ U i₀ ∧ W ≤ V ∧
      ∃ sW : (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).obj.obj (op W),
        (SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op W) sW = 0 ∧
          (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).presheaf.germ W x hxW sW =
            (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).presheaf.germ V x hxV s := by
  have hzeroGerm :
      (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).presheaf.germ V x hxV
          (0 : (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.obj (op V)) = 0 :=
    map_zero _
  obtain ⟨W, hxW, iWV, _, hEq⟩ :=
    (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).presheaf.germ_eq x hxV hxV
      ((SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op V) s) 0
      (hy.trans hzeroGerm.symm)
  have hEqZero :
      (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map iWV.op
          ((SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op V) s) = 0 := by
    rw [hEq, map_zero]
  have hxCover : x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  rw [Opens.mem_iSup] at hxCover
  obtain ⟨i₀, hxi₀⟩ := hxCover
  let W' : Opens X := W ⊓ U i₀
  have hxW' : x ∈ W' := ⟨hxW, hxi₀⟩
  have hW'W : W' ≤ W := inf_le_left
  have hW'V : W' ≤ V := hW'W.trans iWV.le
  let s' : (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).obj.obj (op W') :=
    (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).obj.map (homOfLE hW'V).op s
  have hDiffRestrict :
      (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map (homOfLE hW'V).op
          ((SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op V) s) = 0 := by
    calc
      _ = (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map (homOfLE hW'W).op
          ((Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map iWV.op
            ((SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op V) s)) := by
        change (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map _ _ =
          ((Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map _ ≫
            (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map _) _
        rw [← (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map_comp]
        exact ConcreteCategory.congr_hom
          (congrArg (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map (Subsingleton.elim _ _)) _
      _ = 0 := by rw [hEqZero, map_zero]
  have hs' : (SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op W') s' = 0 := by
    calc
      _ = (Terms.TopCat.Sheaf.cechTerm F U (n + 2)).obj.map (homOfLE hW'V).op
          ((SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.app (op V) s) := by
        exact ConcreteCategory.congr_hom
          ((SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom.naturality (homOfLE hW'V).op) s
      _ = 0 := hDiffRestrict
  exact ⟨i₀, W', hxW', inf_le_right, hW'V, s', hs',
    (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).presheaf.germ_res_apply (homOfLE hW'V) x hxW' s⟩

private theorem exists_stalk_preimage_cechDifferential (hU : ⨆ i, U i = ⊤)
    (n : ℕ) (x : X) (y : (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).presheaf.stalk x)
    (hy : (Presheaf.stalkFunctor AddCommGrpCat x).map
      (SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1)).hom y = 0) :
    ∃ t : (Terms.TopCat.Sheaf.cechTerm F U n).presheaf.stalk x,
      (Presheaf.stalkFunctor AddCommGrpCat x).map
        (SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom t = y := by
  obtain ⟨V, hxV, s, rfl⟩ :=
    (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).presheaf.exists_germ_eq y
  rw [Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨i₀, W, hxW, hWi₀, _, sW, hsW, hGerm⟩ :=
    exists_cechCycle_restriction F U hU n x hxV s hy
  obtain ⟨t, ht⟩ :=
    LocalContraction.TopCat.Sheaf.exists_preimage_cechDifferential_of_le U F i₀ hWi₀ n sW hsW
  refine ⟨(Terms.TopCat.Sheaf.cechTerm F U n).presheaf.germ W x hxW t, ?_⟩
  change (Presheaf.stalkFunctor AddCommGrpCat x).map
      (SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom
        ((Terms.TopCat.Sheaf.cechTerm F U n).presheaf.germ W x hxW t) =
    (Terms.TopCat.Sheaf.cechTerm F U (n + 1)).presheaf.germ V x hxV s
  rw [Presheaf.stalkFunctor_map_germ_apply, ht]
  exact hGerm

/-- If the opens `U i` cover the whole space, the sheaf-level Cech complex is exact in
every positive degree. -/
theorem cechShortComplex_exact (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (ShortComplex.mk (SheafDifferential.TopCat.Sheaf.cechDifferential F U n) (SheafDifferential.TopCat.Sheaf.cechDifferential F U (n + 1))
      (SheafComplex.TopCat.Sheaf.cechDifferential_comp F U n)).Exact := by
  rw [exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  exact exists_stalk_preimage_cechDifferential F U hU n x

end OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveExact.TopCat.Sheaf
