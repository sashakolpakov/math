import OAI.Analysis.Calculus.Current.Quaternion

namespace OAI.Analysis.Calculus.Current

noncomputable section

theorem quaternionDivergence_finset_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Index d → (Index d → ℝ) → (Index d → ℂ) → Quaternion ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ)
    (hR : ∀ j ∈ s, ∀ a, DifferentiableAt ℝ (fun t : ℝ => F j a (realLine x a t) z) 0)
    (hI : ∀ j ∈ s, ∀ a c, DifferentiableAt ℝ
      (fun t : ℝ => F j a x (imaginaryLine z (Pi.single a c) t)) 0) :
    quaternionDivergence (fun a x z => ∑ j ∈ s, F j a x z) x z =
      ∑ j ∈ s, quaternionDivergence (F j) x z := by
  have hr (a : Index d) :
      deriv (fun t : ℝ => ∑ j ∈ s, F j a (realLine x a t) z) 0 =
        ∑ j ∈ s, deriv (fun t : ℝ => F j a (realLine x a t) z) 0 :=
    (HasDerivAt.fun_sum (fun j hj => (hR j hj a).hasDerivAt)).deriv
  have hi (a : Index d) (c : ℂ) :
      deriv (fun t : ℝ => ∑ j ∈ s, F j a x (imaginaryLine z (Pi.single a c) t)) 0 =
        ∑ j ∈ s, deriv (fun t : ℝ => F j a x (imaginaryLine z (Pi.single a c) t)) 0 :=
    (HasDerivAt.fun_sum (fun j hj => (hI j hj a c).hasDerivAt)).deriv
  unfold quaternionDivergence quaternionRealD quaternionImagD
  simp_rw [hr, hi]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_comm

theorem differentiableAt_wavePairedQuaternion_real {d : ℕ} (κ κ' cR cI : ℝ)
    (v v' : Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) :
    DifferentiableAt ℝ
      (fun t : ℝ => wavePairedQuaternion κ κ' cR cI v v' (realLine x a t) z a b) 0 := by
  apply (hasDerivAt_quaternionPair
    ((hasDerivAt_phaseF_line cR cI (phaseDifference κ κ' v v') x a).ofReal_comp.const_mul
      (pairedC κ κ' v v' z a b))
    ((hasDerivAt_phaseG_line cR cI (phaseDifference κ κ' v v') x a).ofReal_comp.const_mul
      (pairedE κ κ' v v' z a b))).differentiableAt

theorem differentiableAt_wavePairedQuaternion_imag {d : ℕ} (κ κ' cR cI : ℝ)
    (v v' : Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (a b : Index d) (c : ℂ) :
    DifferentiableAt ℝ
      (fun t : ℝ => wavePairedQuaternion κ κ' cR cI v v' x
        (imaginaryLine z (Pi.single a c) t) a b) 0 := by
  have hc : DifferentiableAt ℝ (fun w => wavePairedC κ κ' cR cI v v' x w a b) z :=
    (differentiableAt_pairedC κ κ' v v' z hY a b).mul_const _
  have he : DifferentiableAt ℝ (fun w => wavePairedE κ κ' cR cI v v' x w a b) z :=
    (differentiableAt_pairedE κ κ' v v' z hY a b).mul_const _
  exact (hasDerivAt_quaternionPair
    (hasDerivAt_function_line _ z _ hc) (hasDerivAt_function_line _ z _ he)).differentiableAt

/-- Finite superpositions retain every mixed-frequency term and remain
divergence free. The summands are the full Hermitian paired currents. -/
theorem wavePairedQuaternion_finset_divergence {d : ℕ} {ι : Type*} (s : Finset ι)
    (κ κ' cR cI : ι → ℝ) (v v' : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    quaternionDivergence (fun a q w => ∑ j ∈ s,
      wavePairedQuaternion (κ j) (κ' j) (cR j) (cI j) (v j) (v' j) q w a b) x z = 0 := by
  rw [quaternionDivergence_finset_sum s _ x z
    (fun j _ a => differentiableAt_wavePairedQuaternion_real _ _ _ _ _ _ x z a b)
    (fun j _ a c => differentiableAt_wavePairedQuaternion_imag _ _ _ _ _ _ x z hY a b c)]
  apply Finset.sum_eq_zero
  intro j _
  exact wavePairedQuaternion_divergence _ _ _ _ _ _ x z hY b

end
end OAI.Analysis.Calculus.Current
