import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramFrontendBounds

namespace OAI.Algorithms

/-! Input-only closure of the physical parameter/cache/export costs, including
the exact binary word lengths used by the subsequent offset producer. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BinaryArithmetic Bank Circuit Asymptotic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Args := Input × (Fin 8 → ℕ)
def inputMeasure (a : Args) := Layout.inputMeasure a.1 a.2
def nativeCost (a : Args) := Execute.runtimeBound a.1 a.2
def guarded (a : Args) := Execute.guardedModel a.1 a.2
def inputEnvelope (a : Args) := inputMeasure a+nativeCost a+loopCap a.1+5

theorem inputMeasure_pos (a : Args) : 1 ≤ inputMeasure a := by
  have := (magnitude_ge a.1).1
  dsimp [inputMeasure,Layout.inputMeasure]
  omega

theorem nativeCost_poly : Poly inputMeasure nativeCost := by
  obtain ⟨C,d,h⟩ := Execute.runtime_ordinary
  refine ⟨C,d,fun a => ?_⟩
  exact (Nat.le_add_right (nativeCost a) 1).trans (h a.1 a.2)

theorem loopCap_poly : Poly inputMeasure (fun a => loopCap a.1) := by
  apply (Poly.mul (Poly.const inputMeasure 1000000) (Poly.pow (Poly.self inputMeasure) 6)).mono
  intro a
  have hm : magnitude a.1 ≤ inputMeasure a := by dsimp [inputMeasure,Layout.inputMeasure]; omega
  exact Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hm 6)

theorem inputEnvelope_poly : Poly inputMeasure inputEnvelope :=
  Poly.add inputMeasure_pos
    (Poly.add inputMeasure_pos (Poly.add inputMeasure_pos (Poly.self _) nativeCost_poly) loopCap_poly)
    (Poly.const _ 5)

theorem bitBound_le_runtime (x : Input) (l : Fin 8 → ℕ) :
    Execute.bitBound x l ≤ Execute.runtimeBound x l := by
  dsimp [Execute.runtimeBound]
  omega

theorem guarded_length_le (a : Args) (j : Fin 64) : (guarded a).len j ≤ nativeCost a := by
  by_cases hj : j.val < 44
  · change (if j.val < 44 then _ else _) ≤ _
    rw [ite_eq_left hj]
    exact (Execute.final_lengths_le a.1 a.2 j).trans (bitBound_le_runtime a.1 a.2)
  · simp [guarded,Execute.guardedModel,hj]

theorem guarded_core (a : Args) :
    (guarded a).val 0=a.1.ambient ∧ (guarded a).val 5=a.1.factors ∧
    (guarded a).val 18=(produce a.1).r ∧ (guarded a).val 21=(produce a.1).Q ∧
    (guarded a).val 29=(produce a.1).R := by
  have h0 := Execute.guardedModel_input a.1 a.2 0
  have h5 := Execute.guardedModel_input a.1 a.2 5
  have h18 := Execute.guardedModel_radius a.1 a.2
  have h21 := Execute.guardedModel_public a.1 a.2 4
  have h29 := Execute.guardedModel_public a.1 a.2 6
  obtain ⟨_,_,_,_,hQ,_,hR,_⟩ := Layout.model_core_values a.1 a.2
  refine ⟨?_,?_,h18,?_,?_⟩
  · simpa [guarded,Layout.initialValues] using h0
  · simpa [guarded,Layout.initialValues] using h5
  · exact h21.trans hQ
  · exact h29.trans hR

theorem small_parameters_le (x : Input) :
    (produce x).r ≤ loopCap x ∧ (produce x).Q ≤ loopCap x ∧
      (produce x).R ≤ loopCap x+4 := by
  obtain ⟨_,hL,_,hoperand,_⟩ := loop_operands_le_cap x
  refine ⟨(layoutR_le_L x.freeCount).trans hL,?_,?_⟩
  · exact (Nat.div_le_self _ _).trans hL
  · exact Nat.add_le_add_right ((Nat.sqrt_le_self _).trans hoperand) 4

theorem guarded_envelope (a : Args) :
    (∀ j,(guarded a).len j ≤ inputEnvelope a) ∧
    (∀ j∈smallPorts,(guarded a).val j ≤ inputEnvelope a) ∧ 0 < (guarded a).val 18 := by
  obtain ⟨h0,h5,hr,hQ,hR⟩ := guarded_core a
  obtain ⟨hrB,hQB,hRB⟩ := small_parameters_le a.1
  have hbase : a.1.ambient ≤ inputMeasure a ∧ a.1.factors ≤ inputMeasure a := by
    dsimp [inputMeasure,Layout.inputMeasure,magnitude]
    omega
  have hrad := produce_r_ge_two a.1
  refine ⟨fun j => (guarded_length_le a j).trans (by dsimp [inputEnvelope]; omega),?_,?_⟩
  · intro j hj
    simp only [smallPorts,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl
    · rw [h0]; dsimp [inputEnvelope]; omega
    · rw [h5]; dsimp [inputEnvelope]; omega
    · rw [hr]; dsimp [inputEnvelope]; omega
    · rw [hQ]; dsimp [inputEnvelope]; omega
    · rw [hR]; dsimp [inputEnvelope]; omega
  · omega

def exportCost (a : Args) := Exports.prepareBudget (guarded a)

theorem exportCost_poly : Poly inputMeasure exportCost := by
  apply (Poly.compose inputMeasure_pos inputEnvelope_poly postMajorant_poly).mono
  intro a
  obtain ⟨hl,hv,hr⟩ := guarded_envelope a
  exact prepareBudget_bound (guarded a) (inputEnvelope a) hl hv hr

theorem guarded_length_poly (j : Fin 64) : Poly inputMeasure (fun a => (guarded a).len j) :=
  nativeCost_poly.mono (fun a => guarded_length_le a j)

theorem guarded_cutoff_poly : Poly inputMeasure (fun a => (guarded a).val 29) :=
  inputEnvelope_poly.mono (fun a => (guarded_envelope a).2.1 29 (by simp [smallPorts]))

def offsetCost (a : Args) := 5000*(2*(guarded a).val 29+1)^2*
  ((guarded a).len 3+(guarded a).len 21+(guarded a).len 29+11)^2

theorem offsetCost_poly : Poly inputMeasure offsetCost := by
  have hR := Poly.add inputMeasure_pos
    (Poly.mul (Poly.const inputMeasure 2) guarded_cutoff_poly) (Poly.const _ 1)
  have hL := Poly.add inputMeasure_pos
    (Poly.add inputMeasure_pos
      (Poly.add inputMeasure_pos (guarded_length_poly 3) (guarded_length_poly 21))
      (guarded_length_poly 29)) (Poly.const _ 11)
  exact Poly.mul (Poly.mul (Poly.const inputMeasure 5000) (Poly.pow hR 2)) (Poly.pow hL 2)

/-- The offset producer receives actual exported binary B/Q/R words. Include
all three physical length caps and the numeric exponent R in one bound. -/
def bundle (a : Args) := nativeCost a+exportCost a+
  (guarded a).len 3+(guarded a).len 21+(guarded a).len 29+(guarded a).val 29+1+offsetCost a

theorem bundle_poly : Poly inputMeasure bundle :=
  Poly.add inputMeasure_pos (Poly.add inputMeasure_pos
    (Poly.add inputMeasure_pos
      (Poly.add inputMeasure_pos
        (Poly.add inputMeasure_pos
          (Poly.add inputMeasure_pos (Poly.add inputMeasure_pos nativeCost_poly exportCost_poly)
            (guarded_length_poly 3)) (guarded_length_poly 21)) (guarded_length_poly 29))
      guarded_cutoff_poly) (Poly.const _ 1)) offsetCost_poly

def CountsBound (x : Input) (S : ℕ) : Prop :=
  ∀ i : Fin 8,Layout.initialValues x (i.castAdd 56) ≤ S

theorem inputMeasure_le (x : Input) (l : Fin 8 → ℕ) (S : ℕ)
    (hv : CountsBound x S) (hl : ∀ i,l i ≤ S) : inputMeasure (x,l) ≤ 16*(S+1) := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  change x.ambient ≤ S at h0
  change x.freeCount ≤ S at h1
  change x.clauses ≤ S at h2
  change x.occurrence ≤ S at h3
  change x.arity ≤ S at h4
  change x.factors ≤ S at h5
  change x.width ≤ S at h6
  change x.incidences ≤ S at h7
  have hsum : (∑ i,l i) ≤ 8*S := by
    calc
      _ ≤ ∑ i : Fin 8,S := Finset.sum_le_sum (fun i _ => hl i)
      _ = _ := by simp
  dsimp [inputMeasure,Layout.inputMeasure,magnitude]
  omega

/-- One pair of constants works for every measured query and every padding
of its eight binary inputs. No produced-value or produced-length premise. -/
theorem uniform_bundle_polynomial :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      CountsBound x S → (∀ i,l i ≤ S) → bundle (x,l) ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := bundle_poly
  refine ⟨C*16^d,d,?_⟩
  intro x l S hv hl
  calc
    bundle (x,l) ≤ C*(inputMeasure (x,l))^d := h (x,l)
    _ ≤ C*(16*(S+1))^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (inputMeasure_le x l S hv hl) d)
    _ = (C*16^d)*(S+1)^d := by rw [mul_pow,Nat.mul_assoc]

/-- Solver-facing uniform bound: source instruction costs plus the three
actual offset-input word-length caps and its numeric exponent. -/
theorem uniform_polynomial :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      CountsBound x S → (∀ i,l i ≤ S) →
      Execute.runtimeBound x l+Exports.prepareBudget (Execute.guardedModel x l) ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).len 3 ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).len 21 ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).len 29 ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).val 29 ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := uniform_bundle_polynomial
  refine ⟨C,d,?_⟩
  intro x l S hv hl
  have hb := h x l S hv hl
  dsimp [bundle,nativeCost,exportCost,guarded] at hb
  omega

/-- The exact offset-model expression used by the frontend postlude is also
bounded by the same input-only ordinary-polynomial method. -/
theorem uniform_offset_polynomial :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      CountsBound x S → (∀ i,l i ≤ S) →
      Execute.runtimeBound x l+Exports.prepareBudget (Execute.guardedModel x l)+
        5000*(2*(Execute.guardedModel x l).val 29+1)^2*
          ((Execute.guardedModel x l).len 3+(Execute.guardedModel x l).len 21+
            (Execute.guardedModel x l).len 29+11)^2 ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := uniform_bundle_polynomial
  refine ⟨C,d,?_⟩
  intro x l S hv hl
  have hb := h x l S hv hl
  dsimp [bundle,nativeCost,exportCost,guarded,offsetCost] at hb
  omega

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
