import OAI.Analysis.Calculus.Current.WaveDivergence

namespace OAI.Analysis.Calculus.Current

noncomputable section

def quaternionPair (C E : ℂ) : Quaternion ℝ := complexK C + complexK E * qi

def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩

theorem hasDerivAt_complexK {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => complexK (f s)) (complexK f') t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  have hh := (hr.smul_const (1 : Quaternion ℝ)).fun_add
    (hi.smul_const (complexK Complex.I))
  convert hh using 1
  · funext s
    ext <;> simp [complexK]
  · ext <;> simp [complexK]

theorem hasDerivAt_quaternionPair {C E : ℝ → ℂ} {C' E' : ℂ} {t : ℝ}
    (hC : HasDerivAt C C' t) (hE : HasDerivAt E E' t) :
    HasDerivAt (fun s => quaternionPair (C s) (E s)) (quaternionPair C' E') t :=
  (hasDerivAt_complexK hC).fun_add ((hasDerivAt_complexK hE).mul_const qi)

theorem deriv_quaternionPair {C E : ℝ → ℂ} {t : ℝ}
    (hC : DifferentiableAt ℝ C t) (hE : DifferentiableAt ℝ E t) :
    deriv (fun s => quaternionPair (C s) (E s)) t =
      quaternionPair (deriv C t) (deriv E t) :=
  (hasDerivAt_quaternionPair hC.hasDerivAt hE.hasDerivAt).deriv

theorem quaternionPair_divergence_algebra (C0 E0 Cr Er Ci Ei : ℂ) :
    quaternionPair C0 E0 - qi * quaternionPair Cr Er - qj * quaternionPair Ci Ei =
      quaternionPair (C0 + (star Er + Complex.I * star Ei))
        (E0 - (star Cr + Complex.I * star Ci)) := by
  ext <;> simp [quaternionPair, complexK, qi, qj] <;> ring

theorem barD_star {d : ℕ} (f : (Index d → ℂ) → ℂ) (z : Index d → ℂ)
    (hf : DifferentiableAt ℝ f z) (a : Index d) :
    barD (fun w => star (f w)) z a =
      star (deriv (fun t : ℝ => f (imaginaryLine z (Pi.single a 1) t)) 0) +
        Complex.I * star (deriv (fun t : ℝ => f (imaginaryLine z (Pi.single a Complex.I) t)) 0) := by
  have h1 := hasDerivAt_function_line f z (Pi.single a 1) hf
  have hi := hasDerivAt_function_line f z (Pi.single a Complex.I) hf
  simp only [barD, h1.star.deriv, hi.star.deriv, h1.deriv, hi.deriv]

def quaternionRealD {d : ℕ} (F : (Index d → ℝ) → (Index d → ℂ) → Quaternion ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a : Index d) : Quaternion ℝ :=
  deriv (fun t : ℝ => F (realLine x a t) z) 0

def quaternionImagD {d : ℕ} (F : (Index d → ℝ) → (Index d → ℂ) → Quaternion ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a : Index d) (c : ℂ) : Quaternion ℝ :=
  deriv (fun t : ℝ => F x (imaginaryLine z (Pi.single a c) t)) 0

/-- The three-real-slot Fueter divergence for a quaternion-valued column. -/
def quaternionDivergence {d : ℕ}
    (F : Index d → (Index d → ℝ) → (Index d → ℂ) → Quaternion ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) : Quaternion ℝ :=
  ∑ a, (quaternionRealD (F a) x z a - qi * quaternionImagD (F a) x z a 1 -
    qj * quaternionImagD (F a) x z a Complex.I)

theorem quaternionDivergence_split {d : ℕ}
    (C E : Index d → (Index d → ℝ) → (Index d → ℂ) → ℂ)
    (x : Index d → ℝ) (z : Index d → ℂ)
    (hCr : ∀ a, DifferentiableAt ℝ (fun t : ℝ => C a (realLine x a t) z) 0)
    (hEr : ∀ a, DifferentiableAt ℝ (fun t : ℝ => E a (realLine x a t) z) 0)
    (hCi : ∀ a, DifferentiableAt ℝ (C a x) z)
    (hEi : ∀ a, DifferentiableAt ℝ (E a x) z) :
    quaternionDivergence (fun a x z => quaternionPair (C a x z) (E a x z)) x z =
      quaternionPair
        (∑ a, (realD (fun q => C a q z) x a + barD (fun w => star (E a x w)) z a))
        (∑ a, (realD (fun q => E a q z) x a - barD (fun w => star (C a x w)) z a)) := by
  have ha (a : Index d) :
      quaternionRealD (fun x z => quaternionPair (C a x z) (E a x z)) x z a -
        qi * quaternionImagD (fun x z => quaternionPair (C a x z) (E a x z)) x z a 1 -
        qj * quaternionImagD (fun x z => quaternionPair (C a x z) (E a x z)) x z a Complex.I =
      quaternionPair (realD (fun q => C a q z) x a + barD (fun w => star (E a x w)) z a)
        (realD (fun q => E a q z) x a - barD (fun w => star (C a x w)) z a) := by
    unfold quaternionRealD quaternionImagD realD
    rw [deriv_quaternionPair (hCr a) (hEr a),
      deriv_quaternionPair (hasDerivAt_function_line _ z _ (hCi a)).differentiableAt
        (hasDerivAt_function_line _ z _ (hEi a)).differentiableAt,
      deriv_quaternionPair (hasDerivAt_function_line _ z _ (hCi a)).differentiableAt
        (hasDerivAt_function_line _ z _ (hEi a)).differentiableAt,
      quaternionPair_divergence_algebra, barD_star _ z (hEi a), barD_star _ z (hCi a)]
  unfold quaternionDivergence
  simp_rw [ha]
  simp only [quaternionPair, map_sum, map_add, map_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]

def wavePairedQuaternion {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) : Quaternion ℝ :=
  quaternionPair (wavePairedC κ κ' cR cI v v' x z a b)
    (wavePairedE κ κ' cR cI v v' x z a b)

/-- The actual quaternionic divergence of each oscillatory Hermitian pair is zero. -/
theorem wavePairedQuaternion_divergence {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    quaternionDivergence (fun a => fun q w => wavePairedQuaternion κ κ' cR cI v v' q w a b)
      x z = 0 := by
  have hCr (a : Index d) : DifferentiableAt ℝ
      (fun t : ℝ => wavePairedC κ κ' cR cI v v' (realLine x a t) z a b) 0 :=
    ((hasDerivAt_phaseF_line cR cI (phaseDifference κ κ' v v') x a).ofReal_comp.const_mul
      (pairedC κ κ' v v' z a b)).differentiableAt
  have hEr (a : Index d) : DifferentiableAt ℝ
      (fun t : ℝ => wavePairedE κ κ' cR cI v v' (realLine x a t) z a b) 0 :=
    ((hasDerivAt_phaseG_line cR cI (phaseDifference κ κ' v v') x a).ofReal_comp.const_mul
      (pairedE κ κ' v v' z a b)).differentiableAt
  have hCi (a : Index d) : DifferentiableAt ℝ
      (fun w => wavePairedC κ κ' cR cI v v' x w a b) z :=
    (differentiableAt_pairedC κ κ' v v' z hY a b).mul_const _
  have hEi (a : Index d) : DifferentiableAt ℝ
      (fun w => wavePairedE κ κ' cR cI v v' x w a b) z :=
    (differentiableAt_pairedE κ κ' v v' z hY a b).mul_const _
  rw [show (fun a q w => wavePairedQuaternion κ κ' cR cI v v' q w a b) =
      (fun a q w => quaternionPair (wavePairedC κ κ' cR cI v v' q w a b)
        (wavePairedE κ κ' cR cI v v' q w a b)) from rfl,
    quaternionDivergence_split _ _ x z hCr hEr hCi hEi,
    wavePaired_divergence_first κ κ' cR cI v v' x z hY,
    wavePaired_divergence_second κ κ' cR cI v v' x z hY]
  simp [quaternionPair]

end
end OAI.Analysis.Calculus.Current
