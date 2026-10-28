/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafZeroExact.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleLifting

/-! # Zero Cycle Stalks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleStalks.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

theorem exists_cechZeroCycle_restriction (hU : ⨆ i, U i = ⊤) (x : X)
    {V : Opens X} (hxV : x ∈ V) (s : (IntrinsicCech.SheafTerms.cechTerm F U 0).obj.obj (op V))
    (hy : (IntrinsicCech.SheafTerms.cechTerm F U 1).presheaf.germ V x hxV
      ((SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s) = 0) :
    ∃ (i₀ : ι) (W : Opens X) (hxW : x ∈ W), W ≤ U i₀ ∧ W ≤ V ∧
      ∃ sW : (IntrinsicCech.SheafTerms.cechTerm F U 0).obj.obj (op W),
        (SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op W) sW = 0 ∧
          (IntrinsicCech.SheafTerms.cechTerm F U 0).presheaf.germ W x hxW sW =
            (IntrinsicCech.SheafTerms.cechTerm F U 0).presheaf.germ V x hxV s := by
  have hzeroGerm :
      (IntrinsicCech.SheafTerms.cechTerm F U 1).presheaf.germ V x hxV
          (0 : (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.obj (op V)) = 0 :=
    map_zero _
  obtain ⟨W, hxW, iWV, _, hEq⟩ :=
    (IntrinsicCech.SheafTerms.cechTerm F U 1).presheaf.germ_eq x hxV hxV
      ((SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s) 0
      (hy.trans hzeroGerm.symm)
  have hEqZero :
      (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map iWV.op
          ((SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s) = 0 := by
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
  let s' : (IntrinsicCech.SheafTerms.cechTerm F U 0).obj.obj (op W') :=
    (IntrinsicCech.SheafTerms.cechTerm F U 0).obj.map (homOfLE hW'V).op s
  have hDiffRestrict :
      (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map (homOfLE hW'V).op
          ((SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s) = 0 := by
    calc
      _ = (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map (homOfLE hW'W).op
          ((IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map iWV.op
            ((SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s)) := by
        change (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map _ _ =
          ((IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map _ ≫
            (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map _) _
        exact ConcreteCategory.congr_hom
          ((congrArg (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map (Subsingleton.elim _ _)).trans
            ((IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map_comp _ _)) _
      _ = 0 := by rw [hEqZero, map_zero]
  have hs' : (SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op W') s' = 0 := by
    calc
      _ = (IntrinsicCech.SheafTerms.cechTerm F U 1).obj.map (homOfLE hW'V).op
          ((SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s) := by
        exact ConcreteCategory.congr_hom
          ((SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.naturality (homOfLE hW'V).op) s
      _ = 0 := hDiffRestrict
  exact ⟨i₀, W', hxW', inf_le_right, hW'V, s', hs',
    (IntrinsicCech.SheafTerms.cechTerm F U 0).presheaf.germ_res_apply (homOfLE hW'V) x hxW' s⟩

theorem exists_stalk_preimage_cechAugmentation (hU : ⨆ i, U i = ⊤)
    (x : X) (y : (IntrinsicCech.SheafTerms.cechTerm F U 0).presheaf.stalk x)
    (hy : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom y = 0) :
    ∃ t : F.presheaf.stalk x,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom t = y := by
  obtain ⟨V, hxV, s, rfl⟩ :=
    (IntrinsicCech.SheafTerms.cechTerm F U 0).presheaf.exists_germ_eq y
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨i₀, W, hxW, hWi₀, _, sW, hsW, hGerm⟩ :=
    exists_cechZeroCycle_restriction F U hU x hxV s hy
  obtain ⟨t, ht⟩ := ZeroCycleLifting.IntrinsicCech.exists_preimage_cechAugmentation_of_le F U i₀ hWi₀ sW hsW
  refine ⟨F.presheaf.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom (F.presheaf.germ W x hxW t) =
    (IntrinsicCech.SheafTerms.cechTerm F U 0).presheaf.germ V x hxV s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
  exact hGerm

/-- If the opens `U i` cover the whole space, the augmented sheaf-level Cech complex is
exact at degree zero. -/
theorem cechAugmentedShortComplex_exact (hU : ⨆ i, U i = ⊤) :
    (SheafAugmentation.IntrinsicCech.cechAugmentedShortComplex F U).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  exact exists_stalk_preimage_cechAugmentation F U hU x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleStalks.IntrinsicCech
