import OAI.Analysis.PDE.Elliptic.Boundary.Third.Jet
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffOperators

noncomputable section
open Set
open scoped Matrix.Norms.Elementwise BoundedContinuousFunction
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Dirichlet

local instance thirdRecoveryFirstGroup {m : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance thirdRecoveryFirstSpace {m : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance thirdRecoverySecondGroup {m : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance thirdRecoverySecondSpace {m : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance

theorem matrix_entry_holder_norm_le {X : Type*} [MetricSpace X] {m : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin m) (Fin m) ℝ) α) (i j : Fin m) :
    ‖OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Schauder.matrixEntryCLM i j) A‖ ≤ ‖A‖ := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (norm_nonneg A)
  · intro x
    change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j‖ ≤ ‖A‖
    exact ((norm_le_pi_norm (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i) j).trans
      (norm_le_pi_norm (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) i)).trans (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le A x)
  · intro x y
    change ‖(OAI.Analysis.Normed.Function.Holder.HolderMap.value A x-OAI.Analysis.Normed.Function.Holder.HolderMap.value A y) i j‖ ≤ _
    exact ((norm_le_pi_norm ((OAI.Analysis.Normed.Function.Holder.HolderMap.value A x-OAI.Analysis.Normed.Function.Holder.HolderMap.value A y) i) j).trans
      (norm_le_pi_norm (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x-OAI.Analysis.Normed.Function.Holder.HolderMap.value A y) i)).trans
        (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le A x y)

theorem exists_local_third_holder {m : ℕ} {α μ N : ℝ}
    (hα : 0 ≤ α) (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (S : Set (EuclideanSpace ℝ (Fin m)))
      (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 3 u → ∀ k : Fin m,
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      ‖A‖ ≤ N → ∀ R : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α,
      ∀ J Q, 0 ≤ J → 0 ≤ Q → ‖R‖ ≤ Q →
      (∀ i, i ≠ k → ∀ x : S,
        ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x‖ ≤ J) →
      (∀ i, i ≠ k → ∀ x y : S,
        ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x-
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) y‖ ≤
            J*dist x y^α) →
      (∀ x : S, μ ≤ OAI.Analysis.Normed.Function.Holder.HolderMap.value A x k k) →
      (∀ x : S, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A)
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) →
      ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap S
          (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ]
            EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α,
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) ∧
        ‖T‖ ≤ C*(J+Q) := by
  classical
  obtain ⟨C, hC, hthird⟩ := exists_uniform_third_holder (I := Fin m) hα hμ hN
  refine ⟨C, hC, ?_⟩
  intro S u hu k A hAn R J Q hJ hQ hRn hbn hbh hdiag he
  let E := EuclideanSpace ℝ (Fin m)
  let w (i : Fin m) := OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)
  let B (i : Fin m) : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α := by
    by_cases hi : i = k
    · exact 0
    · have hw : ContDiff ℝ 2 (w i) :=
        OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) _
      have hd : ContDiff ℝ 1 (fderiv ℝ (w i)) := hw.fderiv_right (by norm_num)
      have hc : Continuous (fun x : S => fderiv ℝ (fderiv ℝ (w i)) x) :=
        (hd.continuous_fderiv one_ne_zero).comp continuous_subtype_val
      let v : S →ᵇ (E →L[ℝ] E →L[ℝ] ℝ) :=
        BoundedContinuousFunction.ofNormedAddCommGroup _ hc J (hbn i hi)
      have hh : ∀ x y : S, ‖v x-v y‖ ≤ J*dist x y^α := hbh i hi
      exact OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hh
  have hB (i) (hi : i ≠ k) (x : S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (B i) x =
      fderiv ℝ (fderiv ℝ (w i)) x := by simp only [B, dite_eq_right hi]; rfl
  have hBn (i) (hi : i ≠ k) : ‖B i‖ ≤ J := by
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα hJ
    · intro x
      rw [hB i hi]
      exact hbn i hi x
    · intro x y
      rw [hB i hi, hB i hi]
      exact hbh i hi x y
  let Ar := OAI.Analysis.PDE.Schauder.holderIsometricPullback hα (Subtype.val : S → E) isometry_subtype_coe A
  let Ac (p : Fin m × Fin m) := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Schauder.matrixEntryCLM p.1 p.2) Ar
  have hAc (p) : ‖Ac p‖ ≤ N := (matrix_entry_holder_norm_le hα Ar p.1 p.2).trans
    ((OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα (Subtype.val : S → E) isometry_subtype_coe A).trans hAn)
  let Rr := OAI.Analysis.PDE.Schauder.holderIsometricPullback hα (Subtype.val : S → E) isometry_subtype_coe R
  have hRr : ‖Rr‖ ≤ Q := (OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα
    (Subtype.val : S → E) isometry_subtype_coe R).trans hRn
  exact hthird S u hu k (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) Ac Rr B (fun _ _ => rfl) hAc hB
    J Q hJ hQ hBn hRr hdiag he

end OAI.Analysis.PDE.Elliptic
