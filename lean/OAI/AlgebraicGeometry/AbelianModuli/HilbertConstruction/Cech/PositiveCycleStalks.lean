/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafPositiveExact.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleStalks

/-! # Positive Cycle Stalks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PositiveCycleStalks.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

theorem exists_cechCycle_restriction (hU : ⨆ i, U i = ⊤) (n : ℕ) (x : X)
    {V : Opens X} (hxV : x ∈ V)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V))
    (hy : (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).presheaf.germ V x hxV
      ((SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s) = 0) :
    ∃ (i₀ : ι) (W : Opens X) (hxW : x ∈ W), W ≤ U i₀ ∧ W ≤ V ∧
      ∃ sW : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op W),
        (SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op W) sW = 0 ∧
          (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).presheaf.germ W x hxW sW =
            (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).presheaf.germ V x hxV s := by
  have hzeroGerm :
      (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).presheaf.germ V x hxV
          (0 : (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.obj (op V)) = 0 :=
    map_zero _
  obtain ⟨W, hxW, iWV, _, hEq⟩ :=
    (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).presheaf.germ_eq x hxV hxV
      ((SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s) 0
      (hy.trans hzeroGerm.symm)
  have hEqZero :
      (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map iWV.op
          ((SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s) = 0 := by
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
  let s' : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op W') :=
    (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.map (homOfLE hW'V).op s
  have hDiffRestrict :
      (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map (homOfLE hW'V).op
          ((SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s) = 0 := by
    calc
      _ = (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map (homOfLE hW'W).op
          ((IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map iWV.op
            ((SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s)) := by
        change (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map _ _ =
          ((IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map _ ≫
            (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map _) _
        rw [← (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map_comp]
        exact ConcreteCategory.congr_hom
          (congrArg (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map (Subsingleton.elim _ _)) _
      _ = 0 := by rw [hEqZero, map_zero]
  have hs' : (SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op W') s' = 0 := by
    calc
      _ = (IntrinsicCech.SheafTerms.cechTerm F U (n + 2)).obj.map (homOfLE hW'V).op
          ((SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s) := by
        exact ConcreteCategory.congr_hom
          ((SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.naturality (homOfLE hW'V).op) s
      _ = 0 := hDiffRestrict
  exact ⟨i₀, W', hxW', inf_le_right, hW'V, s', hs',
    (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).presheaf.germ_res_apply (homOfLE hW'V) x hxW' s⟩

theorem exists_stalk_preimage_cechDifferential (hU : ⨆ i, U i = ⊤)
    (n : ℕ) (x : X) (y : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).presheaf.stalk x)
    (hy : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom y = 0) :
    ∃ t : (IntrinsicCech.SheafTerms.cechTerm F U n).presheaf.stalk x,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (SheafDifferential.IntrinsicCech.cechDifferential F U n).hom t = y := by
  obtain ⟨V, hxV, s, rfl⟩ :=
    (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).presheaf.exists_germ_eq y
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨i₀, W, hxW, hWi₀, _, sW, hsW, hGerm⟩ :=
    exists_cechCycle_restriction F U hU n x hxV s hy
  obtain ⟨t, ht⟩ :=
    LocalContraction.IntrinsicCech.exists_preimage_cechDifferential_of_le U F i₀ hWi₀ n sW hsW
  refine ⟨(IntrinsicCech.SheafTerms.cechTerm F U n).presheaf.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (SheafDifferential.IntrinsicCech.cechDifferential F U n).hom
        ((IntrinsicCech.SheafTerms.cechTerm F U n).presheaf.germ W x hxW t) =
    (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).presheaf.germ V x hxV s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
  exact hGerm

/-- If the opens `U i` cover the whole space, the sheaf-level Cech complex is exact in
every positive degree. -/
theorem cechShortComplex_exact (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (ShortComplex.mk (SheafDifferential.IntrinsicCech.cechDifferential F U n) (SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1))
      (IntrinsicCech.SheafComplex.cechDifferential_comp F U n)).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  exact exists_stalk_preimage_cechDifferential F U hU n x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PositiveCycleStalks.IntrinsicCech
