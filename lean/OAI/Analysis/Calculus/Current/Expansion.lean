import OAI.Analysis.Calculus.Current.Amplitudes

namespace OAI.Analysis.Calculus.Current

noncomputable section

def modeCurrentTerm {d : ℕ} (κ κ' cR cI dR dI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) : Quaternion ℝ :=
  complexK (tangentField v z a) *
    (star (modeAmplitude κ cR cI v x z) * modeAmplitude κ' dR dI v' x z) *
      star (complexK (tangentField v' z b))

theorem modeCurrentTerm_pair {d : ℕ} (κ κ' cR cI dR dI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) (a b : Index d) :
    modeCurrentTerm κ κ' cR cI dR dI v v' x z a b +
        modeCurrentTerm κ' κ dR dI cR cI v' v x z a b =
      wavePairedQuaternion κ κ' (crossReal cR cI dR dI) (crossImag cR cI dR dI)
        v v' x z a b := by
  let f : ℝ := gaussianField κ κ' v v' z *
    phaseF (crossReal cR cI dR dI) (crossImag cR cI dR dI) (phaseDifference κ κ' v v') x
  let g : ℝ := gaussianField κ κ' v v' z *
    phaseG (crossReal cR cI dR dI) (crossImag cR cI dR dI) (phaseDifference κ κ' v v') x
  have hp : star (modeAmplitude κ cR cI v x z) * modeAmplitude κ' dR dI v' x z =
      (f : Quaternion ℝ) + (g : Quaternion ℝ) * complexK (movingUnit z) * qi :=
    modeAmplitude_cross κ κ' cR cI dR dI v v' x z hY
  have hp' : star (modeAmplitude κ' dR dI v' x z) * modeAmplitude κ cR cI v x z =
      (f : Quaternion ℝ) - (g : Quaternion ℝ) * complexK (movingUnit z) * qi := by
    have hh := congrArg star hp
    simp only [star_mul, star_star] at hh
    rw [hh]
    ext <;> simp [complexK, qi] <;> ring
  unfold modeCurrentTerm
  rw [hp, hp', paired_current_expansion]
  simp only [wavePairedQuaternion, quaternionPair, wavePairedC, wavePairedE, pairedC, pairedE,
    f, g, Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm]

theorem phaseF_scale {d : ℕ} (r cR cI : ℝ) (L x : Index d → ℝ) :
    phaseF (r * cR) (r * cI) L x = r * phaseF cR cI L x := by unfold phaseF; ring

theorem phaseG_scale {d : ℕ} (r cR cI : ℝ) (L x : Index d → ℝ) :
    phaseG (r * cR) (r * cI) L x = r * phaseG cR cI L x := by unfold phaseG; ring

theorem wavePairedQuaternion_scale {d : ℕ} (r κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) :
    wavePairedQuaternion κ κ' (r * cR) (r * cI) v v' x z a b =
      (r : Quaternion ℝ) * wavePairedQuaternion κ κ' cR cI v v' x z a b := by
  simp only [wavePairedQuaternion, quaternionPair, wavePairedC, wavePairedE,
    phaseF_scale, phaseG_scale, Complex.ofReal_mul]
  ext <;> simp [complexK, qi] <;> ring

def modeCurrent {d : ℕ} {ι : Type*} [Fintype ι] (κ cR cI : ι → ℝ)
    (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) :
    Matrix (Index d) (Index d) (Quaternion ℝ) :=
  currentMatrix (ratio z) (fun j i => (v j i : ℂ))
    (fun j => modeAmplitude (κ j) (cR j) (cI j) (v j) x z)

theorem modeCurrent_expand {d : ℕ} {ι : Type*} [Fintype ι] (κ cR cI : ι → ℝ)
    (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) :
    modeCurrent κ cR cI v x z a b =
      ∑ j, ∑ k, modeCurrentTerm (κ j) (κ k) (cR j) (cI j) (cR k) (cI k)
        (v j) (v k) x z a b := by
  simp only [modeCurrent, currentMatrix, OAI.Analysis.Calculus.Quaternion.outer, currentColumn,
    star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum, modeCurrentTerm, tangentField]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_assoc]

theorem modeCurrent_paired_expansion {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (a b : Index d) :
    modeCurrent κ cR cI v x z a b =
      ∑ p : ι × ι, wavePairedQuaternion (κ p.1) (κ p.2)
        ((1 / 2 : ℝ) * crossReal (cR p.1) (cI p.1) (cR p.2) (cI p.2))
        ((1 / 2 : ℝ) * crossImag (cR p.1) (cI p.1) (cR p.2) (cI p.2))
        (v p.1) (v p.2) x z a b := by
  simp_rw [wavePairedQuaternion_scale, ← modeCurrentTerm_pair _ _ _ _ _ _ _ _ x z hY]
  rw [Fintype.sum_prod_type]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j k => modeCurrentTerm (κ k) (κ j) (cR k) (cI k) (cR j) (cI j)
    (v k) (v j) x z a b)]
  rw [← modeCurrent_expand]
  rw [← add_mul]
  have hh : ((1 / 2 : ℝ) : Quaternion ℝ) + ((1 / 2 : ℝ) : Quaternion ℝ) = 1 := by
    rw [← Quaternion.coe_add, show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num,
      Quaternion.coe_one]
  rw [hh, one_mul]

end
end OAI.Analysis.Calculus.Current
