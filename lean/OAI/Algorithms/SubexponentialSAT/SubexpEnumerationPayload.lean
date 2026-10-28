import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationCode
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram

namespace OAI.Algorithms

/-!
# A fixed machine emitting the encoded increment schedule

The input contains the actual one-pass increment payload and the unary number
of outer basepoints.  `BlockCopyProgram.program` preserves that payload and
emits one copy for each outer basepoint.  The payloads below are computed from
the supplied vector arrays, and their lengths follow from the proved coset
cardinalities rather than from numerical premises about execution.

This is the increment schedule used by the separate color sums.  It does not
construct the basis arrays, add outer basepoints, or evaluate the summands.
The cost of preparing the input stacks remains a separate obligation.
-/

namespace SubexponentialSAT.SubexpEnumerationPayload

open scoped BigOperators
open SubexpLayoutSpec

/-- One field coordinate occupies this many binary cells. -/
def scalarWidth (p : ℕ) : ℕ := Nat.log 2 p + 1

/-- The canonical little-endian binary word for an actual field element. -/
def scalarBits {p : ℕ} [Fact p.Prime] (x : ZMod p) : List Bool :=
  SubexpLiftRing.fixedBits (scalarWidth p) x.val

@[simp] theorem scalarBits_length {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    (scalarBits x).length = scalarWidth p :=
  SubexpLiftRing.fixedBits_length _ _

theorem scalarBits_value {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    BinaryArithmetic.toNat (scalarBits x) = x.val := by
  apply SubexpLiftRing.toNat_fixedBits_of_lt
  exact x.val_lt.trans (Nat.lt_pow_succ_log_self Nat.one_lt_two p)

theorem scalarBits_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (scalarBits (p := p)) := by
  intro a b h
  have hv := congrArg BinaryArithmetic.toNat h
  simp only [scalarBits_value] at hv
  simpa using congrArg (fun n : ℕ => (n : ZMod p)) hv

def scalarCode (p : ℕ) [Fact p.Prime] : StackEncoding.BlockCode (ZMod p) where
  width := scalarWidth p
  width_pos := Nat.zero_lt_succ _
  block := scalarBits
  length_block := scalarBits_length
  injective_block := scalarBits_injective

/-- Coordinate words in increasing ambient-coordinate order. -/
def vectorBits {D p : ℕ} [Fact p.Prime] (x : Fin D → ZMod p) : List Bool :=
  StackEncoding.encodeDataStack (scalarCode p) (List.ofFn x)

@[simp] theorem vectorBits_length {D p : ℕ} [Fact p.Prime]
    (x : Fin D → ZMod p) : (vectorBits x).length = D * scalarWidth p := by
  simp [vectorBits, scalarCode]

theorem vectorBits_injective {D p : ℕ} [Fact p.Prime] :
    Function.Injective (vectorBits (D := D) (p := p)) := by
  intro a b h
  exact List.ofFn_injective
    (StackEncoding.encodeDataStack_injective (scalarCode p) h)

/-- Fixed-width vector words concatenated in their supplied list order. -/
def vectorsBits {D p : ℕ} [Fact p.Prime] (xs : List (Fin D → ZMod p)) :
    List Bool := xs.flatMap vectorBits

@[simp] theorem vectorsBits_nil {D p : ℕ} [Fact p.Prime] :
    vectorsBits ([] : List (Fin D → ZMod p)) = [] := rfl

@[simp] theorem vectorsBits_append {D p : ℕ} [Fact p.Prime]
    (xs ys : List (Fin D → ZMod p)) :
    vectorsBits (xs ++ ys) = vectorsBits xs ++ vectorsBits ys := by
  simp [vectorsBits]

@[simp] theorem vectorsBits_length {D p : ℕ} [Fact p.Prime]
    (xs : List (Fin D → ZMod p)) :
    (vectorsBits xs).length = xs.length * (D * scalarWidth p) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa only [vectorsBits, List.flatMap_cons, List.length_append,
        vectorBits_length, List.length_cons, Nat.add_mul, Nat.one_mul,
        Nat.add_comm] using congrArg (fun n => D * scalarWidth p + n) ih

theorem vectorsBits_repeated {D p : ℕ} [Fact p.Prime]
    (n : ℕ) (xs : List (Fin D → ZMod p)) :
    vectorsBits ((List.replicate n xs).flatten) =
      Subexp.BlockCopyProgram.copies n (vectorsBits xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ', List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, vectorsBits_append, ih,
        Subexp.BlockCopyProgram.copies_succ]

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
  {P : Factor.Pattern (Fin D) F} {c : Parameters p k Δ r tau}
  {L : Layout (E := E) P c} {t : Fin c.Q}

/-- Every color's increment list is scanned separately in increasing color
order.  Shared vectors, such as zero, remain distinct visits. -/
def innerVectors (data : EnumerationData L t) : List (Fin D → ZMod p) :=
  (List.ofFn (SubexpEnumerationCode.innerIncrements data)).flatten

theorem innerVectors_length (data : EnumerationData L t) :
    (innerVectors data).length = ∑ g, data.innerCount g := by
  simp [innerVectors, List.length_flatten, List.sum_ofFn]

def innerPayload (data : EnumerationData L t) : List Bool :=
  vectorsBits (innerVectors data)

theorem innerPayload_length (data : EnumerationData L t) :
    (innerPayload data).length = (∑ g, data.innerCount g) * (D * scalarWidth p) := by
  rw [innerPayload, vectorsBits_length, innerVectors_length]

/-- The actual list of increment visits, one complete pass per outer datum. -/
def workVectors (data : EnumerationData L t) : List (Fin D → ZMod p) :=
  (List.replicate (SubexpEnumerationCode.outerBases data).length
    (innerVectors data)).flatten

theorem workVectors_length (data : EnumerationData L t) :
    (workVectors data).length = data.iterationCount := by
  simp [workVectors, List.length_flatten, innerVectors_length,
    EnumerationData.iterationCount]

def workPayload (data : EnumerationData L t) : List Bool :=
  vectorsBits (workVectors data)

theorem workPayload_eq_copies (data : EnumerationData L t) :
    workPayload data = Subexp.BlockCopyProgram.copies
      (SubexpEnumerationCode.outerBases data).length (innerPayload data) :=
  vectorsBits_repeated _ _

theorem workPayload_length (data : EnumerationData L t) :
    (workPayload data).length = data.iterationCount * (D * scalarWidth p) := by
  rw [workPayload, vectorsBits_length, workVectors_length]

/-- The machine's emitted cells are tied to the actual coset dimensions. -/
theorem workPayload_length_exact (data : EnumerationData L t) :
    (workPayload data).length =
      (p ^ (D - ∑ g, Module.finrank (ZMod p) (L.K t g)) *
        ∑ g, p ^ Module.finrank (ZMod p) (L.K t g)) *
      (D * (Nat.log 2 p + 1)) := by
  rw [workPayload_length, data.iterationCount_eq]
  simp only [SubexpCosetCount.iterationCount, Fintype.card_fin, scalarWidth]

/-- Prepared input: stack 0 is the one-pass payload; stack 1 is the output
suffix; stack 2 is empty; stack 3 is the unary number of outer basepoints. -/
def preparedState (data : EnumerationData L t) (suffix : List Bool) :
    Subexp.BlockCopyProgram.Data :=
  Subexp.BlockCopyProgram.initialState
    (SubexpEnumerationCode.outerBases data).length (innerPayload data) suffix

def finishedState (data : EnumerationData L t) (suffix : List Bool) :
    Subexp.BlockCopyProgram.Data :=
  Subexp.BlockCopyProgram.data false false (innerPayload data)
    (workPayload data ++ suffix) []

def traceSteps (data : EnumerationData L t) : ℕ :=
  (SubexpEnumerationCode.outerBases data).length *
    (7 * (innerPayload data).length + 7) + 3

/-- A trace of the same twelve-label Boolean-stack program for every p, D,
number of colors, and supplied array. No evaluation callback is assumed. -/
theorem program_trace (data : EnumerationData L t) (suffix : List Bool) :
    BitProgram.Trace Subexp.BlockCopyProgram.program (traceSteps data)
      ((preparedState data suffix).withPC
        (some Subexp.BlockCopyProgram.program.entry))
      ((finishedState data suffix).withPC none) := by
  simpa only [traceSteps, preparedState, finishedState, workPayload_eq_copies] using
    Subexp.BlockCopyProgram.program_trace
      (SubexpEnumerationCode.outerBases data).length (innerPayload data) suffix

/-- The output-stack length includes the unchanged suffix. -/
theorem finished_output_length (data : EnumerationData L t) (suffix : List Bool) :
    ((finishedState data suffix).stacks 1).length =
      data.iterationCount * (D * scalarWidth p) + suffix.length := by
  simp [finishedState, Subexp.BlockCopyProgram.data, workPayload_length]

theorem traceSteps_eq (data : EnumerationData L t) :
    traceSteps data = 7 * data.iterationCount * (D * scalarWidth p) +
      7 * data.outerCount + 3 := by
  rw [traceSteps, innerPayload_length, SubexpEnumerationCode.outerBases_length]
  simp only [EnumerationData.iterationCount]
  ring

theorem outerCount_le_iterationCount (data : EnumerationData L t) :
    data.outerCount ≤ data.iterationCount := by
  let g : Fin r := ⟨0, by have := c.r_ge_two; omega⟩
  have hg : 1 ≤ data.innerCount g := by
    have := (data.zeroIndex g).isLt
    omega
  have hs : 1 ≤ ∑ h, data.innerCount h :=
    hg.trans (Finset.single_le_sum (fun h _ => Nat.zero_le (data.innerCount h))
      (Finset.mem_univ g))
  simpa only [EnumerationData.iterationCount, Nat.mul_one] using
    Nat.mul_le_mul_left data.outerCount hs

theorem traceSteps_le (data : EnumerationData L t) :
    traceSteps data ≤ 7 * data.iterationCount * (D * scalarWidth p + 1) + 3 := by
  rw [traceSteps_eq]
  have h := Nat.mul_le_mul_left 7 (outerCount_le_iterationCount data)
  calc
    _ ≤ 7 * data.iterationCount * (D * scalarWidth p) +
        7 * data.iterationCount + 3 := by omega
    _ = _ := by ring

/-- The proved coset bound now controls actual finite-control steps. The
linear encoding factor retains the variable coordinate width. -/
theorem traceSteps_le_real (data : EnumerationData L t) :
    (traceSteps data : ℝ) ≤
      7 * ((r : ℝ) * (p : ℝ) ^ (SubexpCosetCount.alpha r (tau : ℝ) * D)) *
        ((D * scalarWidth p : ℕ) + 1) + 3 := by
  have hsteps : (traceSteps data : ℝ) ≤
      7 * (data.iterationCount : ℝ) * ((D * scalarWidth p : ℕ) + 1) + 3 := by
    exact_mod_cast traceSteps_le data
  have hcount : (data.iterationCount : ℝ) ≤
      (r : ℝ) * (p : ℝ) ^ (SubexpCosetCount.alpha r (tau : ℝ) * D) := by
    simpa only [Fintype.card_fin] using data.iterationCount_bound
  calc
    _ ≤ _ := hsteps
    _ ≤ _ := by gcongr

theorem workPayload_length_le_real (data : EnumerationData L t) :
    ((workPayload data).length : ℝ) ≤
      ((r : ℝ) * (p : ℝ) ^ (SubexpCosetCount.alpha r (tau : ℝ) * D)) *
        (D * scalarWidth p : ℕ) := by
  rw [workPayload_length, Nat.cast_mul]
  have hcount : (data.iterationCount : ℝ) ≤
      (r : ℝ) * (p : ℝ) ^ (SubexpCosetCount.alpha r (tau : ℝ) * D) := by
    simpa only [Fintype.card_fin] using data.iterationCount_bound
  exact mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)

/-- A run of the fixed primitive binary machine supplied by the verified
compiler. Its overhead depends only on the fixed copy program. -/
theorem program_primitive (data : EnumerationData L t) (suffix : List Bool) :
    Computation.RunsIn (BitProgram.primitive Subexp.BlockCopyProgram.program).step
      (BitProgram.primitiveOverhead Subexp.BlockCopyProgram.program * traceSteps data)
      (BitProgram.primitiveCfg Subexp.BlockCopyProgram.program
        ((preparedState data suffix).withPC
          (some Subexp.BlockCopyProgram.program.entry)))
      (BitProgram.primitiveCfg Subexp.BlockCopyProgram.program
        ((finishedState data suffix).withPC none)) :=
  BitProgram.primitive_trace _ (program_trace data suffix)

theorem primitive_cost_le_real (data : EnumerationData L t) :
    ((BitProgram.primitiveOverhead Subexp.BlockCopyProgram.program *
        traceSteps data : ℕ) : ℝ) ≤
      (BitProgram.primitiveOverhead Subexp.BlockCopyProgram.program : ℝ) *
        (7 * ((r : ℝ) * (p : ℝ) ^ (SubexpCosetCount.alpha r (tau : ℝ) * D)) *
          ((D * scalarWidth p : ℕ) + 1) + 3) := by
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (traceSteps_le_real data) (Nat.cast_nonneg _)

end SubexponentialSAT.SubexpEnumerationPayload

end OAI.Algorithms
