import OAI.Analysis.PDE.Concentration.Physical.Geometry
import OAI.Analysis.PDE.Concentration.Physical.Positivity
import OAI.Analysis.Calculus.Current.Flux

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Green
open scoped Matrix Matrix.Norms.Elementwise

private theorem fin_cases_one {d : ℕ} {β : Sort*} (a : β) (f : Fin (d + 1) → β) :
    Fin.cases a f (1 : Fin (d + 2)) = f 0 := by
  rw [← Fin.succ_zero_eq_one]
  rfl

theorem nullRotation_column_abs_le (d : ℕ) (i : Fin (d + 2)) :
    ∑ j, |nullRotation d j i| ≤ 2 := by
  have hs : 1 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hq := inv_le_one_of_one_le₀ hs
  have hq0 : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  all_goals simp [nullRotation, Fin.sum_univ_succ, fin_cases_one, abs_of_nonneg hq0, apply_ite]
  all_goals linarith

theorem norm_physicalVector_le {d : ℕ} (v : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    ‖physicalVector v‖ ≤ 2 * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, star (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) j i) * v (nullIndexEquiv d j)‖ ≤ _
  calc
    _ ≤ ∑ j, ‖star (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) j i) * v (nullIndexEquiv d j)‖ := norm_sum_le _ _
    _ = ∑ j, |nullRotation d j i| * ‖v (nullIndexEquiv d j)‖ := by
      simp [OAI.Analysis.PDE.Dirichlet.realLift_apply, norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j, |nullRotation d j i| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v _) (abs_nonneg _)
    _ = (∑ j, |nullRotation d j i|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right (nullRotation_column_abs_le d i) (norm_nonneg _)

theorem physicalMatrix_normal_row_bound {d : ℕ}
    {M : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)} (hM : M.IsHermitian)
    (g : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    ‖star (physicalVector g) ᵥ* physicalMatrix M‖ ≤ 2 * ‖star g ᵥ* M‖ := by
  have hP : (physicalMatrix M).IsHermitian :=
    matrixConjugationCLM_isHermitian _ (nullMatrixReindex_isHermitian hM)
  rw [← hP, ← Matrix.star_mulVec, norm_star, physicalMatrix_mulVec]
  have h := norm_physicalVector_le (M *ᵥ g)
  rwa [← norm_star (M *ᵥ g), Matrix.star_mulVec, hM] at h

theorem physicalPacketCurrent_normal_flux_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ᵥ*
      physicalPacketCurrent h a κ cR cI v x‖ ≤
        2 * ‖star (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a (physicalToNullCurrentPoint d x).2) ᵥ*
          OAI.Analysis.Calculus.Current.sourceRegularizedCurrent h a κ cR cI v
            (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2‖ := by
  rw [physicalFullDefining_gradient d a x hx, physicalPacketCurrent_eq_physicalMatrix]
  exact physicalMatrix_normal_row_bound
    (OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_isHermitian h a hh κ cR cI v _ _ hx) _

theorem physicalPacketCurrent_lateral_power_flux_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h a R C k b M : ℝ) (hh : 0 < h) (hha : h ≤ a)
    (hR0 : 0 ≤ R) (hC0 : 0 ≤ C) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hay : a ≤ ‖(physicalToNullCurrentPoint d x).2 none‖)
    (hR : ∀ j, κ j / ‖(physicalToNullCurrentPoint d x).2 none‖ ≤ R)
    (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0)
    (hpoly : (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C) ≤ h ^ (-b))
    (hlog : (b + M / 2) * Real.log h⁻¹ ≤ k * ‖(physicalToNullCurrentPoint d x).2 none‖ / 3200) :
    ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ᵥ*
      physicalPacketCurrent h a κ cR cI v x‖ ≤
        (40 * ((d : ℝ) + 2) * ((d : ℝ) + 1) ^ 2) * h ^ (M - 1) := by
  have hY : (physicalToNullCurrentPoint d x).2 none ≠ 0 :=
    norm_pos_iff.mp ((hh.trans_le hha).trans_le hay)
  have hr' : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a (physicalToNullCurrentPoint d x).2 = 0 :=
    (congrFun (physicalFullDefining_eq_null d a) x).symm.trans hr
  have hb := OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_lateral_power_flux_bound h a R C k b M hh hha hR0 hC0
    κ cR cI v hκ hk (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2
    hay hR hC hv hr' hpoly hlog
  calc
    _ ≤ 2 * ‖star (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a (physicalToNullCurrentPoint d x).2) ᵥ*
        OAI.Analysis.Calculus.Current.sourceRegularizedCurrent h a κ cR cI v
          (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2‖ :=
      physicalPacketCurrent_normal_flux_bound h a hh κ cR cI v x hY
    _ ≤ 2 * ((20 * ((d : ℝ) + 2) * ((d : ℝ) + 1) ^ 2) * h ^ (M - 1)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end OAI.Analysis.PDE.Concentration
