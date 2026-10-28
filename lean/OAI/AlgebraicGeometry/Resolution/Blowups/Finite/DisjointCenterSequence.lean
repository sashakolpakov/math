import OAI.AlgebraicGeometry.Resolution.Blowups.Global.FactorCenterDrop
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.DisjointCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.CenterPermissibility

/-! # Disjoint Center Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A finite family of disjoint permissible integral centers is cleared by an actual global sequence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialSequence.Construction.SmoothFixedControlSequence

universe u v

theorem Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod {X Y : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (S : Finset ι) (f : Y ⟶ X) :
    (∏ j ∈ S, D j).comap f = ∏ j ∈ S, (D j).comap f := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact Scheme.IdealSheafData.comap_top f
  | @insert j S hj ih => rw [Finset.prod_insert hj, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, ih, Finset.prod_insert hj]

def Global.MonomialSequence.Construction.SmoothFixedControlSequence.integralCenters
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J) : Prop :=
  match T with
  | @terminal _ _ _ _ _ _ => True
  | @blowup _ _ _ _ _ _ I _ _ _ _ _ tail => IsIntegral I.subscheme ∧ tail.integralCenters

theorem Finite.DisjointCenterSequence.Construction.exists_finite_disjoint_integral_center_sequence (N : ℕ) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
      (K : Fin N → X.IdealSheafData),
      (∀ i, K i ≠ ⊥) → (∀ i, IsIntegral (K i).subscheme) →
      (∀ i, Smooth ((K i).subschemeι ≫ f)) →
      (∀ i j, i ≠ j → K i ⊔ K j = ⊤) →
      (∀ i, J ≤ K i ^ (n + 1)) →
      (∏ i, K i) ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n →
      ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J, T.integralCenters := by
  induction N with
  | zero =>
      intro X _ _ f _ J n K _ _ _ _ _ hprod
      have ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤ := by
        simpa only [Fin.prod_univ_zero, Scheme.IdealSheafData.one_eq_top, top_le_iff] using hprod
      refine ⟨.terminal (by simpa only [Nat.add_sub_cancel] using ht), ?_⟩
      change True
      trivial
  | succ N ih =>
      intro X _ _ f _ J n K hK hInt hSm hDis hPerm hProd
      let C := K 0
      let L := ∏ i : Fin N, K i.succ
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase C (hK 0)
      let : IsIntegral C.subscheme := hInt 0
      let : Smooth (C.subschemeι ≫ f) := hSm 0
      let : Smooth (π ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f C (hK 0)
      let J' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J (hK 0) (n + 1)
      let K' (i : Fin N) := (K i.succ).comap π
      have hfactor : C * L ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := by
        simpa only [Fin.prod_univ_succ] using hProd
      have hprod' : (∏ i, K' i) ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (π ≫ f) J' n := by
        have h := Global.FactorCenterDrop.Construction.global_factor_center_differential_bound f J C L (hK 0) n hfactor (hPerm 0)
        rw [Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod] at h
        exact h
      have hK' (i : Fin N) : K' i ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot C (K i.succ) (hK 0) (hK i.succ)
      have hInt' (i : Fin N) : IsIntegral (K' i).subscheme :=
        @Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_integral _ _ _ C (K i.succ) (hK 0)
          (hDis 0 i.succ (Fin.succ_ne_zero i).symm) (hInt i.succ)
      have hSm' (i : Fin N) : Smooth ((K' i).subschemeι ≫ (π ≫ f)) :=
        @Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth _ _ _ _ f C (K i.succ) (hK 0)
          (hDis 0 i.succ (Fin.succ_ne_zero i).symm) (hSm i.succ)
      have hDis' (i j : Fin N) (hij : i ≠ j) : K' i ⊔ K' j = ⊤ := by
        change (K i.succ).comap π ⊔ (K j.succ).comap π = ⊤
        rw [← Scheme.IdealSheafData.comap_sup, hDis i.succ j.succ
          (fun h => hij (Fin.succ_injective _ h)), Scheme.IdealSheafData.comap_top]
      have hPerm' (i : Fin N) : J' ≤ K' i ^ (n + 1) :=
        Disjoint.CenterPermissibility.Construction.globalBlowup_preserves_disjoint_center_permissibility C (K i.succ) J (hK 0) (n + 1) (n + 1)
          (hDis i.succ 0 (Fin.succ_ne_zero i)) (hPerm i.succ)
      obtain ⟨tail, htail⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C (hK 0)) (π ≫ f) J' n K' hK' hInt' hSm' hDis' hPerm' hprod'
      exact ⟨.blowup C (hK 0) (Nat.succ_pos n) (hPerm 0) (hSm 0) inferInstance tail,
        hInt 0, htail⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
