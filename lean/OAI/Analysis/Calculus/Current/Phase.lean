import OAI.Analysis.Calculus.Current.Pairs

namespace OAI.Analysis.Calculus.Current

noncomputable section

def realPhaseRow {d : ℕ} (v : Fin d → ℝ) : Index d → ℝ
  | none => -(∑ i, v i * v i) / 2
  | some none => 1
  | some (some i) => v i

theorem realPhaseRow_coe {d : ℕ} (v : Fin d → ℝ) (a : Index d) :
    (realPhaseRow v a : ℂ) = phaseRow (fun i => (v i : ℂ)) a := by
  cases a with
  | none => simp [realPhaseRow, phaseRow]
  | some a => cases a <;> simp [realPhaseRow, phaseRow]

def phaseDifference {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ) (a : Index d) : ℝ :=
  κ' * realPhaseRow v' a - κ * realPhaseRow v a

theorem phaseDifference_tangent_left {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) :
    (∑ a, (phaseDifference κ κ' v v' a : ℂ) * tangentField v z a) =
      crossPhase κ' v' (tangentField v z) := by
  simp only [phaseDifference, Complex.ofReal_sub, Complex.ofReal_mul,
    realPhaseRow_coe, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have hv : ∑ a, phaseRow (fun i => (v i : ℂ)) a * tangentField v z a = 0 :=
    phase_tangent _ _
  rw [hv]
  simp [crossPhase]

theorem phaseDifference_tangent_right {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) :
    (∑ a, (phaseDifference κ κ' v v' a : ℂ) * tangentField v' z a) =
      -crossPhase κ v (tangentField v' z) := by
  simp only [phaseDifference, Complex.ofReal_sub, Complex.ofReal_mul,
    realPhaseRow_coe, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have hv : ∑ a, phaseRow (fun i => (v' i : ℂ)) a * tangentField v' z a = 0 :=
    phase_tangent _ _
  rw [hv]
  simp [crossPhase]

def phaseArgument {d : ℕ} (L x : Index d → ℝ) : ℝ := ∑ a, L a * x a

def realLine {d : ℕ} (x : Index d → ℝ) (a : Index d) (t : ℝ) : Index d → ℝ :=
  fun b => x b + t * (Pi.single a 1 : Index d → ℝ) b

@[simp] theorem realLine_zero {d : ℕ} (x : Index d → ℝ) (a : Index d) :
    realLine x a 0 = x := by ext b; simp [realLine]

theorem hasDerivAt_phaseArgument_line {d : ℕ} (L x : Index d → ℝ) (a : Index d) :
    HasDerivAt (fun t : ℝ => phaseArgument L (realLine x a t)) (L a) 0 := by
  have h (b : Index d) : HasDerivAt (fun t : ℝ => L b * realLine x a t b)
      (L b * (Pi.single a 1 : Index d → ℝ) b) 0 := by
    simpa only [realLine, one_mul, id_eq] using
      ((((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single a 1 : Index d → ℝ) b)).const_add
        (x b)).const_mul (L b))
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => h b)
  simpa [phaseArgument, Pi.single_apply] using hh

def phaseF {d : ℕ} (cR cI : ℝ) (L x : Index d → ℝ) : ℝ :=
  cR * Real.cos (phaseArgument L x) - cI * Real.sin (phaseArgument L x)

def phaseG {d : ℕ} (cR cI : ℝ) (L x : Index d → ℝ) : ℝ :=
  cR * Real.sin (phaseArgument L x) + cI * Real.cos (phaseArgument L x)

theorem hasDerivAt_phaseF_line {d : ℕ} (cR cI : ℝ) (L x : Index d → ℝ) (a : Index d) :
    HasDerivAt (fun t : ℝ => phaseF cR cI L (realLine x a t))
      (-(L a) * phaseG cR cI L x) 0 := by
  have h := hasDerivAt_phaseArgument_line L x a
  convert (h.cos.const_mul cR).fun_sub (h.sin.const_mul cI) using 1
  all_goals (try simp only [realLine_zero, phaseF, phaseG])
  all_goals ring

theorem hasDerivAt_phaseG_line {d : ℕ} (cR cI : ℝ) (L x : Index d → ℝ) (a : Index d) :
    HasDerivAt (fun t : ℝ => phaseG cR cI L (realLine x a t))
      (L a * phaseF cR cI L x) 0 := by
  have h := hasDerivAt_phaseArgument_line L x a
  convert (h.sin.const_mul cR).fun_add (h.cos.const_mul cI) using 1
  all_goals (try simp only [realLine_zero, phaseF, phaseG])
  all_goals ring

theorem phase_contraction_pairedC {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (b : Index d) :
    (∑ a, (phaseDifference κ κ' v v' a : ℂ) * pairedC κ κ' v v' z a b) =
      (gaussianField κ κ' v v' z : ℂ) *
        (crossPhase κ' v' (tangentField v z) * star (tangentField v' z b) -
          crossPhase κ v (tangentField v' z) * star (tangentField v z b)) := by
  calc
    _ = (gaussianField κ κ' v v' z : ℂ) *
        ((∑ a, (phaseDifference κ κ' v v' a : ℂ) * tangentField v z a) *
          star (tangentField v' z b) +
         (∑ a, (phaseDifference κ κ' v v' a : ℂ) * tangentField v' z a) *
          star (tangentField v z b)) := by
      simp only [pairedC, Finset.mul_sum, Finset.sum_mul, mul_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [phaseDifference_tangent_left, phaseDifference_tangent_right]; ring

theorem phase_contraction_pairedE {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (b : Index d) :
    (∑ a, (phaseDifference κ κ' v v' a : ℂ) * pairedE κ κ' v v' z a b) =
      (gaussianField κ κ' v v' z : ℂ) * movingUnit z *
        (crossPhase κ' v' (tangentField v z) * tangentField v' z b +
          crossPhase κ v (tangentField v' z) * tangentField v z b) := by
  calc
    _ = (gaussianField κ κ' v v' z : ℂ) * movingUnit z *
        ((∑ a, (phaseDifference κ κ' v v' a : ℂ) * tangentField v z a) *
          tangentField v' z b -
         (∑ a, (phaseDifference κ κ' v v' a : ℂ) * tangentField v' z a) *
          tangentField v z b) := by
      simp only [pairedE, Finset.mul_sum, Finset.sum_mul, mul_sub, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [phaseDifference_tangent_left, phaseDifference_tangent_right]; ring

end
end OAI.Analysis.Calculus.Current
