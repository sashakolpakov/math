import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafInput
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

/-! Uniform correctness and resources for the fixed native leaf. The final
contract instantiates the actual preparation, marked rounds and accepted
query; only numerical bounds produced by the outer program remain. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

def time (n k localTime bound : ℕ) : ℕ :=
  3624 * bound + 100 * (SparseCountProgram.formulaBound n k + 1) +
    11 * n + localTime + 5479

private theorem dispatch_total_time_le (steps bound localTime body formula n : ℕ)
    (ht : steps ≤ 6 * bound + 100 * (body + 1) + 11 * n +
      (3618 * bound + localTime + 5446) + 33)
    (hbody : body ≤ formula) :
    steps ≤ 3624 * bound + 100 * (formula + 1) + 11 * n + localTime + 5479 := by
  calc
    steps ≤ 6 * bound + 100 * (body + 1) + 11 * n +
        (3618 * bound + localTime + 5446) + 33 := ht
    _ ≤ 6 * bound + 100 * (formula + 1) + 11 * n +
        (3618 * bound + localTime + 5446) + 33 := by gcongr
    _ = 3624 * bound + 100 * (formula + 1) + 11 * n + localTime + 5479 := by ring

/-- The concrete terminal classifier, paid loading and full-word export use
one unchanged global stack cap. The remaining premise is the actual fixed
local command at the loader-produced input, discharged below by its query run. -/
theorem execution {n k parameterBound bound localBound localTime : ℕ}
    (threshold : List Bool) (F : RawCNF n) (a : State 80 1220)
    (hk : 0 < k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hv : Valid k F) (hr : LeafReady k threshold parameterBound F a)
    (hselect : SparsePriority.select (ExecCNF.formulaSet F)
      (BinaryArithmetic.toNat threshold) = none)
    (ha : ∀ i, (a.stacks i).length ≤ bound)
    (hlocalBound : localBound ≤ bound)
    (hclassifier : 101 * SparseCountProgram.formulaBound n k + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound)
    (hlocal : [] ∉ F → F ≠ [] →
      F.length ≤ n * (4 * BinaryArithmetic.toNat threshold ^ (k - 1)) →
      ∀ d : State 40 896,
      d.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      BinaryArithmetic.toNat (d.stacks 786) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) →
      (∀ i, (d.stacks i).length ≤
        SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → d.stacks i = []) →
      (∀ i, d.regs i = false) →
      ∃ steps ≤ localTime, ∃ e, Eval (NativeLeafProgram.localCommand k) steps d e ∧
        e.stacks 788 = countWord (rawCount F) ∧
        ∀ q z, q ≤ steps → Trace (NativeLeafProgram.localProgram k) q
          (d.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
          ∀ i, (z.stacks i).length ≤ localBound) :
    ∃ steps ≤ time n k localTime bound, ∃ e,
      BoundedEval (NativeLeafProgram.command k) steps a e bound ∧ LeafDone F a e := by
  have hbody : (a.stacks 265).length ≤ SparseCountProgram.formulaBound n k := by
    rw [hr.current]
    exact SparseCountProgram.encodeBody_length_le F k hv.literal_nodup hv.clause_nodup
      (formulaSet_width_le F hv.width)
  obtain ⟨steps, ht, e, he, hd⟩ := NativeLeafDispatch.command_execution
    (NativeLeafExecution.command (NativeLeafProgram.localCommand k))
    (3618 * bound + localTime + 5446) bound hr ha (by omega) hpower (by
      intro hz hn hready hframe
      have hm := NativeLeafInput.clauses_le_physical_occurrence F threshold a
        hk hM hv hr hselect hz
      rw [hr.dimension] at hm
      obtain ⟨t, htime, out, hrun, hdone, _, _, _⟩ :=
        NativeLeafExecution.command_execution threshold F _
          (NativeLeafProgram.localCommand k) hv hready hframe hlocalBound
          (hlocal hz hn hm)
      exact ⟨t, htime, out, hrun, hdone⟩)
  refine ⟨steps, ?_, e, he, hd⟩
  unfold time
  exact dispatch_total_time_le steps bound localTime (a.stacks 265).length
    (SparseCountProgram.formulaBound n k) n ht hbody

/-- Uniformly package the actual fixed-command executions for the existing
DFS contract. This is an internal composition lemma, not a final theorem
assuming a counting evaluator. -/
theorem contract_of_local_execution {n k parameterBound bound localBound localTime : ℕ}
    (threshold : List Bool) (hk : 0 < k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hlocalBound : localBound ≤ bound)
    (hclassifier : 101 * SparseCountProgram.formulaBound n k + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound)
    (hlocal : ∀ F : RawCNF n, Valid k F → [] ∉ F → F ≠ [] →
      F.length ≤ n * (4 * BinaryArithmetic.toNat threshold ^ (k - 1)) →
      ∀ d : State 40 896,
      d.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      BinaryArithmetic.toNat (d.stacks 786) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) →
      (∀ i, (d.stacks i).length ≤
        SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → d.stacks i = []) →
      (∀ i, d.regs i = false) →
      ∃ steps ≤ localTime, ∃ e, Eval (NativeLeafProgram.localCommand k) steps d e ∧
        e.stacks 788 = countWord (rawCount F) ∧
        ∀ q z, q ≤ steps → Trace (NativeLeafProgram.localProgram k) q
          (d.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
          ∀ i, (z.stacks i).length ≤ localBound) :
    LeafContract (n := n) k threshold parameterBound (NativeLeafProgram.command k)
      (time n k localTime bound) bound := by
  constructor
  intro F a hv hr hs ha
  exact execution threshold F a hk hM hv hr hs ha hlocalBound hclassifier hpower
    (hlocal F hv)

open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
/-- The actual preparation, same staged rounds and separate accepted query
produce one fixed local leaf run. The time counts every phase, including the
paid accepted staging/cleanup; space uses the maximum of independent caps.
The queried history is exactly the attained history returned by those rounds. -/
theorem local_from_runs {n B : ℕ} (k : ℕ) (F : RawCNF n)
    (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (a base selected middle : State 40 896)
    (prepareSteps roundSteps querySteps L prepareCap roundCap queryCap : ℕ)
    (ep : Eval NativeLeafPreparation.command prepareSteps a base)
    (sp : ∀ t z, t ≤ prepareSteps →
      Trace (compiled NativeLeafPreparation.command 784 788) t
        (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ prepareCap)
    (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
    (hselected : RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
    (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
    (er : Eval (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) roundSteps base selected)
    (sr : StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k))
      (roundSteps + 1) base roundCap)
    (eq : Eval (HighQueryProgram.accepted k) querySteps (AcceptedQueryStage.staged selected) middle)
    (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
      (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
          (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
    (sq : StageSpace (HighQueryProgram.accepted k) querySteps
      (AcceptedQueryStage.staged selected) queryCap) :
    ∃ steps out,
      steps + 1 ≤ prepareSteps + roundSteps + querySteps + 61 * L + 71 ∧
      Eval (NativeLeafProgram.localCommand k) steps a out ∧
      out.stacks = Function.update selected.stacks 788 (countWord (rawCount F)) ∧
      out.stacks 788 = countWord (rawCount F) ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      ∀ t z, t ≤ steps + 1 → Trace (NativeLeafProgram.localProgram k) t
        (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
        ∀ i, (z.stacks i).length ≤
          max prepareCap (max roundCap (max queryCap (1000 * L + 100))) := by
  obtain ⟨steps, out, ht, he, hout, hcount, hbound, _, hp⟩ :=
    NativeLeafRun.continuation_count F hm hB shifts Q hs hQ
      (HighQueryProgram.marked k) (HighQueryProgram.accepted k) base selected middle
      roundSteps querySteps L roundCap queryCap hr hselected ha hn er sr eq hword sq
  obtain ⟨whole, _, hprefix⟩ := NativeLeafRun.command_of_evals
    (HighQueryProgram.marked k) (HighQueryProgram.accepted k) a base out
    prepareSteps steps prepareCap (max roundCap (max queryCap (1000 * L + 100))) ep he sp hp
  exact ⟨prepareSteps + steps, out, by omega, whole, hout, hcount, hbound, hprefix⟩

private theorem final_cap (inputLength prepareCap roundCap K L C d A e : ℕ)
    (hmain : max prepareCap roundCap ≤ max K (A * (inputLength + 1) ^ e))
    (hL : L ≤ C * (inputLength + 1) ^ d) :
    max prepareCap (max roundCap (max K (1000 * L + 100))) ≤
      max K ((A + 1000 * C + 100) * (inputLength + 1) ^ (d + e)) := by
  let P := (inputLength + 1) ^ (d + e)
  have hbase : 1 ≤ inputLength + 1 := by omega
  have hd : (inputLength + 1) ^ d ≤ P := Nat.pow_le_pow_right hbase (by omega)
  have he : (inputLength + 1) ^ e ≤ P := Nat.pow_le_pow_right hbase (by omega)
  have hP : 1 ≤ P := Nat.one_le_pow' _ _
  have hA : A * (inputLength + 1) ^ e ≤ (A + 1000 * C + 100) * P :=
    (Nat.mul_le_mul_left A he).trans (Nat.mul_le_mul_right P (by omega))
  have hmain' := hmain.trans (max_le_max le_rfl hA)
  have hl := hL.trans (Nat.mul_le_mul_left C hd)
  have hfinish : 1000 * L + 100 ≤ (A + 1000 * C + 100) * P := by
    nlinarith only [hl, hP, Nat.zero_le (A * P)]
  exact max_le ((le_max_left _ _).trans hmain')
    (max_le ((le_max_right _ _).trans hmain')
      (max_le (le_max_left _ _) (hfinish.trans (le_max_right _ _))))

/-- The actual preparation, same common-bound selector and paid final count
staging admit one fixed polynomial in the original input length. The genuine
query prefix cap remains separate, with no query duration charged as space. -/
theorem chosen_local_space (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W K : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ started prepared base : State 40 896,
      (∀ i, (started.stacks i).length ≤ startupBound) →
      SqrtLog.LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startupBound +
        NativeLeafSetup.parameterTime m B startupBound
          (started.stacks 782).length (started.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤
        NativeLeafPreparation.retainedBound m B startupBound started prepared) →
      let L := NativeLeafRun.commonBound n m B
        (NativeLeafPreparation.retainedBound m B startupBound started prepared)
      max (max (startupBound + 1)
          (NativeLeafPreparation.continuationSpace m B startupBound started prepared))
        (max (NativeLeafRun.roundsSpace base n m (SqrtLog.SparseCode.distanceDenom m B) L K)
          (max K (1000 * L + 100))) ≤ max K (C * (inputLength + 1) ^ degree) := by
  obtain ⟨C, d, hcommon⟩ :=
    LeafPreparationBudgets.chosen_prepared_common_bound k wordCoefficient wordDegree
  obtain ⟨A, e, hselector⟩ :=
    LeafPreparationBudgets.chosen_prepared_selector_space k wordCoefficient wordDegree
  refine ⟨A + 1000 * C + 100, d + e, ?_⟩
  intro n inputLength m W K hn hm hnI hs B hmB hW startupBound
    started prepared base hstarted hmetadata hprepared hmword hbase L
  have hc := hcommon n inputLength m W hn hm hnI hs hmB hW
    started prepared hstarted hmetadata hprepared
  have hr := hselector n inputLength m W K hn hm hnI hs hmB hW
    started prepared base hstarted hmetadata hprepared hmword hbase
  exact final_cap inputLength _ _ K L C d A e hr ((le_max_right _ _).trans hc)

/-- The actual loader uses exactly the body, ambient word and independent
setup-parameter cap. Their sum is polynomial in the original input length,
with coefficients and degree fixed before the input is chosen. -/
theorem loaded_input_bound (k parameterCoefficient parameterDegree n inputLength parameterBound : ℕ)
    (hn : n ≤ inputLength)
    (hp : parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree) :
    SparseCountProgram.formulaBound n k + (n + 1) + parameterBound ≤
      (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient) *
        (inputLength + 1) ^ (k + 1 + parameterDegree) := by
  let P := (inputLength + 1) ^ (k + 1 + parameterDegree)
  have hb : 1 ≤ inputLength + 1 := by omega
  have hformula := formulaBound_polynomial n k
  have hbase : (n + 1) ^ (k + 1) ≤ P :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ inputLength + 1) (k + 1)).trans
      (Nat.pow_le_pow_right hb (by omega))
  have hparameter : (inputLength + 1) ^ parameterDegree ≤ P :=
    Nat.pow_le_pow_right hb (by omega)
  have hlinear : n + 1 ≤ P := by
    apply (show n + 1 ≤ inputLength + 1 by omega).trans
    simpa only [pow_one] using Nat.pow_le_pow_right hb
      (show 1 ≤ k + 1 + parameterDegree by omega)
  have hf := hformula.trans (Nat.mul_le_mul_left _ hbase)
  have hp' := hp.trans (Nat.mul_le_mul_left parameterCoefficient hparameter)
  change _ ≤ (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient) * P
  nlinarith only [hf, hp', hlinear]

/-- Substitute the real three-word loader cap into the actual local-space
bound. The setup parameter word is the only incoming size datum, and its
producer polynomial fixes all constants before the original input. -/
theorem chosen_loaded_local_space (k parameterCoefficient parameterDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m parameterBound K : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B →
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ started prepared base : State 40 896,
      (∀ i, (started.stacks i).length ≤ startupBound) →
      SqrtLog.LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startupBound +
        NativeLeafSetup.parameterTime m B startupBound
          (started.stacks 782).length (started.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤
        NativeLeafPreparation.retainedBound m B startupBound started prepared) →
      let L := NativeLeafRun.commonBound n m B
        (NativeLeafPreparation.retainedBound m B startupBound started prepared)
      max (max (startupBound + 1)
          (NativeLeafPreparation.continuationSpace m B startupBound started prepared))
        (max (NativeLeafRun.roundsSpace base n m (SqrtLog.SparseCode.distanceDenom m B) L K)
          (max K (1000 * L + 100))) ≤ max K (C * (inputLength + 1) ^ degree) := by
  obtain ⟨C, degree, hcap⟩ := chosen_local_space k
    (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient)
    (k + 1 + parameterDegree)
  refine ⟨C, degree, ?_⟩
  intro n inputLength m parameterBound K hn hm hnI hs hp B hmB W startupBound
    started prepared base hstarted hmetadata hprepared hmword hbase L
  exact hcap n inputLength m W K hn hm hnI hs hmB
    (loaded_input_bound k parameterCoefficient parameterDegree n inputLength parameterBound hnI hp)
    started prepared base hstarted hmetadata hprepared hmword hbase

/-- The ordinary size appearing in the measured staged-round budget is
bounded by the same common L that bounds its actual retained words. -/
theorem common_round_size (n m B R : ℕ) :
    m + SqrtLog.SparseCode.distanceDenom m B + (n + 1) +
      NativeLeafRun.commonBound n m B R + SqrtLog.HashSelect.loopCap n m + 1 ≤
        5 * NativeLeafRun.commonBound n m B R + 1 := by
  let S := HashQueryInputBounds.commonCap n m B R
  have hpow : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hs : S ≤ NativeLeafRun.commonBound n m B R := by
    unfold NativeLeafRun.commonBound
    change S ≤ 16 * S ^ 3
    omega
  dsimp only [S, HashQueryInputBounds.commonCap] at hs
  omega

open SqrtLog HashGreedyProgram.NativeRound in
/-- Apply the fixed-power query replacement to the identical staged budget
used by the actual rounds. The old budget uses a canonical proof-side round
word; the actual machine retains its unary round word. Physical word factors
remain explicit in the old budget until its numerical producer bound is used. -/
theorem staged_rounds_time_substitution
    {n m B R : ℕ} {initial : List (List Bool)} (base : State 40 896)
    (hr : NativeLeafPreparation.Ready n m B initial base) (hm : 0 < m)
    (queryCost : List Bool → ℕ) (inputLength newQuery oldQuery factor power C d : ℕ)
    (ha : ∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R)
    (hL : NativeLeafRun.commonBound n m B R ≤ C * (inputLength + 1) ^ d)
    (hq : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ newQuery)
    (hnew : newQuery ≤ factor * (oldQuery + inputLength + 1) ^ power) :
    let depth := SparseCode.distanceDenom m B
    let L := NativeLeafRun.commonBound n m B R
    let E := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
      (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
      (depth * (base.stacks 780).length) oldQuery
    NativeLeafRun.roundsTime base n m depth queryCost L ≤
      1000000000 * (5 * C + factor + 3) ^ 5 *
        (E + inputLength + 1) ^ ((d + power + 1) * 5) := by
  intro depth L E
  let Enew := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
    (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
    (depth * (base.stacks 780).length) newQuery
  let X := E + inputLength + 1
  let P := X ^ (d + power + 1)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hiX : inputLength + 1 ≤ X := by dsimp [X]; omega
  have hd : (inputLength + 1) ^ d ≤ P :=
    (Nat.pow_le_pow_left hiX d).trans (Nat.pow_le_pow_right hX (by omega))
  have hp : X ^ (power + 1) ≤ P := Nat.pow_le_pow_right hX (by omega)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ hX
  have hL' : L ≤ C * P := hL.trans (Nat.mul_le_mul_left C hd)
  have hE : Enew ≤ (factor + 1) * X ^ (power + 1) :=
    HashGreedyBudgets.polynomialBudget_substitute_with_input
      (base.stacks 780) (base.stacks 817) (countWord (HashSelect.loopCap n m))
      (HashSelect.loopCap n m) (depth * (base.stacks 780).length)
      oldQuery newQuery factor power inputLength hnew
  have hE' := hE.trans (Nat.mul_le_mul_left (factor + 1) hp)
  have hs := common_round_size n m B R
  have hsum : m + depth + (n + 1) + L + HashSelect.loopCap n m + 1 + Enew + 1 ≤
      (5 * C + factor + 3) * P := by
    change m + depth + (n + 1) + L + HashSelect.loopCap n m + 1 ≤ 5 * L + 1 at hs
    nlinarith only [hs, hL', hE', hP]
  have hround := NativeLeafRun.roundsTime_le_fifth_power base hr hm queryCost L newQuery ha hq
  have hpow := Nat.mul_le_mul_left 1000000000 (Nat.pow_le_pow_left hsum 5)
  apply hround.trans
  simpa only [P, X, mul_pow, ← pow_mul, Nat.mul_assoc] using hpow

open SqrtLog HashGreedyProgram.NativeRound in
/-- Uniformly charge the actual staged rounds to the original all-candidate,
all-mark call count. The actual canonical modulus and saved depth words are
bounded from preparation, including their padding, before substitution. -/
theorem staged_rounds_time_hashCalls (factor power C d : ℕ) :
    ∃ A degree : ℕ, ∀ {n m B R : ℕ} {initial : List (List Bool)} (base : State 40 896),
      NativeLeafPreparation.Ready n m B initial base → 0 < m →
      ∀ (queryCost : List Bool → ℕ) (inputLength newQuery oldQuery : ℕ),
      (∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R) →
      NativeLeafRun.commonBound n m B R ≤ C * (inputLength + 1) ^ d →
      (∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ newQuery) →
      newQuery ≤ factor * (oldQuery + inputLength + 1) ^ power →
      NativeLeafRun.roundsTime base n m (SparseCode.distanceDenom m B) queryCost
        (NativeLeafRun.commonBound n m B R) ≤
        A * (CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) +
          oldQuery + inputLength + 1) ^ degree := by
  have scale (a b y z e q : ℕ) (hz : z ≤ b * y ^ e) :
      a * z ^ q ≤ a * b ^ q * y ^ (e * q) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using
      Nat.mul_le_mul_left a (Nat.pow_le_pow_left hz q)
  let D := (d + power + 1) * 5
  let K := (10000 * 4 ^ 7 + 1) * (C + 1) ^ 14
  refine ⟨(1000000000 * (5 * C + factor + 3) ^ 5) * K ^ D,
    (14 * (d + 1)) * D, ?_⟩
  intro n m B R initial base hr hm queryCost inputLength newQuery oldQuery ha hL hq hnew
  let depth := SparseCode.distanceDenom m B
  let L := NativeLeafRun.commonBound n m B R
  let E := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
    (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
    (depth * (base.stacks 780).length) oldQuery
  let Y := CostAssembly.hashCalls n m depth + oldQuery + inputLength + 1
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  have hIY : inputLength + 1 ≤ Y := by dsimp [Y]; omega
  have hYpow : Y ≤ Y ^ (d + 1) := Nat.le_self_pow (by omega) Y
  have hLpow : L ≤ C * Y ^ (d + 1) :=
    hL.trans (Nat.mul_le_mul_left C
      ((Nat.pow_le_pow_left hIY d).trans (Nat.pow_le_pow_right hY (by omega))))
  have hsum : L + CostAssembly.hashCalls n m depth + oldQuery + 1 ≤
      (C + 1) * Y ^ (d + 1) := by
    have hrest : CostAssembly.hashCalls n m depth + oldQuery + 1 ≤ Y := by dsimp [Y]; omega
    nlinarith only [hLpow, hYpow, hrest]
  let S := HashQueryInputBounds.commonCap n m B R
  have hS : S ≤ L := by
    have hp : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
    change S ≤ 16 * S ^ 3
    omega
  have hdimensions : m ≤ L ∧ depth ≤ L ∧ HashSelect.loopCap n m ≤ L := by
    dsimp only [S, HashQueryInputBounds.commonCap] at hS
    dsimp only [depth]
    omega
  have hc : CounterPrograms.value (base.stacks 780) = 3 * m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.modulus
  have hd : CounterPrograms.value (base.stacks 817) = depth := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.depth
  have he : E ≤ 10000 * 4 ^ 7 * (L + CostAssembly.hashCalls n m depth + oldQuery + 1) ^ 14 :=
    HashGreedyBudgets.canonical_originalBudget_le (base.stacks 780) (base.stacks 817)
      n m depth L oldQuery hm hc hd hdimensions.1 hdimensions.2.1 hdimensions.2.2 (ha 780) (ha 817)
  have he' : E ≤ (10000 * 4 ^ 7) * (C + 1) ^ 14 * Y ^ ((d + 1) * 14) :=
    he.trans (scale (10000 * 4 ^ 7) (C + 1) Y _ (d + 1) 14 hsum)
  have hy' : inputLength + 1 ≤ (C + 1) ^ 14 * Y ^ ((d + 1) * 14) := by
    have hcoeff : 1 ≤ (C + 1) ^ 14 := Nat.one_le_pow' _ _
    have hp : Y ≤ Y ^ ((d + 1) * 14) := Nat.le_self_pow (by omega) Y
    exact (hIY.trans hp).trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right (Y ^ ((d + 1) * 14)) hcoeff)
  have heI : E + inputLength + 1 ≤ K * Y ^ (14 * (d + 1)) := by
    dsimp only [K]
    rw [Nat.mul_comm 14 (d + 1)]
    nlinarith only [he', hy']
  have hround := staged_rounds_time_substitution base hr hm queryCost
    inputLength newQuery oldQuery factor power C d ha hL hq hnew
  exact hround.trans (scale (1000000000 * (5 * C + factor + 3) ^ 5)
    K Y (E + inputLength + 1) (14 * (d + 1)) D heI)

open SqrtLog HashGreedyProgram.NativeRound in
/-- A uniform bound on each actual marked query pays every staged greedy
round at the chosen occurrence threshold. The common physical cap and the
query envelope are fixed before the input and all reached caller states. -/
theorem chosen_rounds_runtimeBound (k commonCoefficient commonDegree : ℕ)
    (queryCoefficient queryExponent : ℝ) (queryDegree : ℕ)
    (hC : 1 ≤ queryCoefficient) (hA : 1 ≤ queryExponent) (hd : 1 ≤ queryDegree) :
    ∃ C A : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ A ∧ 1 ≤ degree ∧
      ∀ n inputLength m R : ℕ, cutoff ≤ n →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B →
      ∀ (initial : List (List Bool)) (base : State 40 896),
      NativeLeafPreparation.Ready n m B initial base → 0 < m →
      ∀ (queryCost : List Bool → ℕ) (queryTime : ℕ),
      (∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R) →
      NativeLeafRun.commonBound n m B R ≤ commonCoefficient * (inputLength + 1) ^ commonDegree →
      (∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ queryTime) →
      queryTime ≤ Nat.ceil (Statement.runtimeBound queryCoefficient queryExponent queryDegree inputLength n) →
      (NativeLeafRun.roundsTime base n m (SparseCode.distanceDenom m B) queryCost
        (NativeLeafRun.commonBound n m B R) : ℝ) ≤
        Statement.runtimeBound C A degree inputLength n := by
  obtain ⟨coefficient, power, hpoly⟩ :=
    staged_rounds_time_hashCalls 1 1 commonCoefficient commonDegree
  obtain ⟨cutoff, htime⟩ := QueryStreamBudgets.chosen_hash_query_polynomial_runtime
    k (coefficient + 1) (power + 1) queryCoefficient queryExponent queryDegree hC hA hd
  refine ⟨((coefficient + 1 : ℕ) : ℝ) * (4 * queryCoefficient) ^ (power + 1),
    ((power + 1 : ℕ) : ℝ) * queryExponent, queryDegree * (power + 1), cutoff, ?_, ?_, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 coefficient)
      (one_le_pow₀ (by linarith))
  · exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 power) hA
  · exact Nat.mul_pos (by omega) (by omega)
  · intro n inputLength m R hn B hmB initial base hr hm queryCost queryTime hb hL hq ht
    apply htime n hn m inputLength queryTime _ hmB ht
    have hp := hpoly base hr hm queryCost inputLength queryTime queryTime hb hL hq (by
      simp only [pow_one, one_mul]
      omega)
    let X := CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) + queryTime + inputLength + 1
    have hX : 1 ≤ X := by dsimp only [X]; omega
    exact hp.trans (Nat.mul_le_mul (Nat.le_succ coefficient)
      (Nat.pow_le_pow_right hX (Nat.le_succ power)))

open SqrtLog SqrtLog.Statement in
/-- The exact four phase costs used by local_from_runs share one runtime
scale, including the separate accepted query and paid final source staging. -/
theorem local_time_runtimeBound
    {Cp Cr Cq Ap Ar Aq : ℝ} (dp dr dq W dw inputLength n : ℕ)
    (prepareSteps roundSteps querySteps whole L : ℕ)
    (hCp : 0 ≤ Cp) (hCr : 0 ≤ Cr) (hCq : 1 ≤ Cq)
    (hAp : 0 ≤ Ap) (hAr : 0 ≤ Ar) (hAq : 0 ≤ Aq)
    (hp : (prepareSteps : ℝ) ≤ runtimeBound Cp Ap dp inputLength n)
    (hr : (roundSteps : ℝ) ≤ runtimeBound Cr Ar dr inputLength n)
    (hq : querySteps ≤ Nat.ceil (runtimeBound Cq Aq dq inputLength n))
    (hL : L ≤ W * (inputLength + 1) ^ dw)
    (hwhole : whole ≤ prepareSteps + roundSteps + querySteps + 61 * L + 71) :
    (whole : ℝ) ≤ runtimeBound (Cp + Cr + 2 * Cq + (61 * W + 71 : ℕ))
      (Ap + Ar + Aq) (dp + dr + dq + dw) inputLength n := by
  have hq' : (querySteps : ℝ) ≤ runtimeBound (2 * Cq) Aq dq inputLength n := by
    rw [runtimeBound_mul_constant]
    exact (Nat.cast_le.mpr hq).trans (Execution.ceil_runtimeBound_le hCq hAq dq inputLength n)
  have hpr := (add_le_add hp hr).trans
    (QueryStreamBudgets.runtimeBound_add_bound Cp Cr Ap Ar dp dr inputLength n hCp hCr hAp hAr)
  have hcore : ((prepareSteps + roundSteps + querySteps : ℕ) : ℝ) ≤
      runtimeBound (Cp + Cr + 2 * Cq) (Ap + Ar + Aq) (dp + dr + dq) inputLength n := by
    simpa only [Nat.cast_add] using (add_le_add hpr hq').trans
      (QueryStreamBudgets.runtimeBound_add_bound (Cp + Cr) (2 * Cq) (Ap + Ar) Aq
        (dp + dr) dq inputLength n (by positivity) (by linarith) (by positivity) hAq)
  have hextra : 61 * L + 71 ≤ (61 * W + 71) * (inputLength + 1) ^ dw := by
    have hpower : 1 ≤ (inputLength + 1) ^ dw := Nat.one_le_pow' _ _
    nlinarith only [hL, hpower]
  have htime := QueryStreamBudgets.polynomial_overhead_runtime
    (Cp + Cr + 2 * Cq) (Ap + Ar + Aq) (dp + dr + dq) (61 * W + 71) dw
    inputLength n (prepareSteps + roundSteps + querySteps) (61 * L + 71)
    (by linarith) (by positivity) hcore hextra
  exact (Nat.cast_le.mpr (show whole ≤ (prepareSteps + roundSteps + querySteps) +
    (61 * L + 71) by omega)).trans htime

open SqrtLog Filter
open scoped Topology

/-- Execute preparation on the actual three loaded words and bind its time,
retained common bound and all-prefix storage to constants chosen before the
input. Both code matrices and the first-query blank workspace are produced
by this run, rather than provided by a successful-code hypothesis. -/
theorem prepared_loaded (k parameterCoefficient parameterDegree : ℕ) :
    ∃ C degree : ℕ, ∃ Ct : ℝ, ∃ exponent timeDegree cutoff : ℕ, 1 ≤ Ct ∧
      ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      ∀ (F : RawCNF n) (a : State 40 896), F ≠ [] → F.length ≤ n * B →
      (∀ i, (a.stacks i).length ≤ W) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
      a.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (a.stacks 785) = n →
      BinaryArithmetic.toNat (a.stacks 786) = B →
      ∃ (steps : ℕ) (started prepared base : State 40 896)
        (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
        let startup := W + NativeLeafSetup.canonicalStartTime n F.length W
        let R := NativeLeafPreparation.retainedBound F.length B startup started prepared
        let L := NativeLeafRun.commonBound n F.length B R
        Eval NativeLeafPreparation.command steps a base ∧
        (steps : ℝ) ≤ Statement.runtimeBound Ct exponent timeDegree inputLength n ∧
        (∀ i, (started.stacks i).length ≤ startup) ∧
        LeafOuterProgram.Metadata F.length B prepared ∧
        (∀ i, (prepared.stacks i).length ≤ startup +
          NativeLeafSetup.parameterTime F.length B startup
            (started.stacks 782).length (started.stacks 786).length) ∧
        NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base ∧
        WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
        SparseCode.HasDistance Q (SparseCode.degree F.length B /
          (100 * B * SparseCode.logSize F.length) + 1) ∧
        base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) ∧
        BinaryArithmetic.toNat (base.stacks 785) = n ∧
        (∀ i, (base.stacks i).length ≤ R) ∧
        (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
          base.stacks i = []) ∧
        L ≤ C * (inputLength + 1) ^ degree ∧
        ∀ t z, t ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) t
          (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
          ∀ i, (z.stacks i).length ≤ C * (inputLength + 1) ^ degree := by
  let wordCoefficient := 3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient
  let wordDegree := k + 1 + parameterDegree
  obtain ⟨C, degree, hcommon⟩ :=
    LeafPreparationBudgets.chosen_prepared_common_bound k wordCoefficient wordDegree
  obtain ⟨Ct, exponent, timeDegree, cutoff₁, hCt, htime⟩ :=
    LeafPreparationBudgets.chosen_preparation_runtimeBound k wordCoefficient wordDegree
  obtain ⟨cutoff₂, hschedule⟩ := Filter.eventually_atTop.mp
    (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨C, degree, Ct, exponent, timeDegree, max (max cutoff₁ cutoff₂) 1, hCt, ?_⟩
  intro n inputLength parameterBound hcut hnI hp B W F a hne hmB ha hempty hformula hn hBword
  have hnpos : 0 < n := by omega
  have hm : 0 < F.length := List.length_pos_iff.mpr hne
  have hs : 1 ≤ sparsifySchedule n := hschedule n (by omega)
  have hB : 0 < B := by
    dsimp only [B]
    have hM := (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    positivity
  have hW : W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree :=
    loaded_input_bound k parameterCoefficient parameterDegree n inputLength parameterBound hnI hp
  obtain ⟨steps, started, prepared, base, shifts, Q, hsteps, he, hstarted, _hmword,
    _hmodulus, hmetadata, hprepared, hready, hgood, hdistance, hframe, hbound, hprefix, hupper⟩ :=
    NativeLeafRun.prepare_raw F a ha hempty hformula hne hB hn hBword
  have hc := hcommon n inputLength F.length W hnpos hm hnI hs hmB hW
    started prepared hstarted hmetadata hprepared
  have ht := htime n inputLength F.length W (by omega) hm hnI hmB hW
    started prepared hstarted hmetadata hprepared
  refine ⟨steps, started, prepared, base, shifts, Q, he, ?_, hstarted, hmetadata,
    hprepared, hready, hgood, hdistance, ?_, ?_, hbound, hupper,
    (Nat.le_max_right _ _).trans hc, ?_⟩
  · exact (Nat.cast_le.mpr hsteps).trans ht
  · exact (hframe 784 (by decide) (by decide)).trans
      (hformula.trans (NativeTerminal.clauseRecords_body F).symm)
  · rw [hframe 785 (by decide) (by decide)]
    exact hn
  · intro t z htz hz i
    exact (hprefix t z htz hz i).trans ((Nat.le_max_left _ _).trans hc)


open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
/-- Every staged greedy round now invokes the genuine fixed marked query.
Time uses an arbitrary finite opaque-word frame; the independent space proof
uses the actual caller/collector cap and the same measured execution. -/
theorem marked_rounds (k C0 d0 : ℕ) (hk : 2 ≤ k) :
    ∃ C E : ℝ, ∃ degree Cs es cutoff : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
      ∀ n inputLength R : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n), Valid k F → 0 < F.length → F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (base : State 40 896),
      NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        base.stacks i = []) →
      let L := NativeLeafRun.commonBound n F.length B R
      L ≤ C0 * (inputLength + 1) ^ d0 →
      let queryTime := Nat.ceil (Statement.runtimeBound C E degree inputLength n)
      let K := max (Cs * (inputLength + 1) ^ es) (3 * L + 2)
      ∃ steps selected,
        steps ≤ NativeLeafRun.roundsTime base n F.length (SparseCode.distanceDenom F.length B)
          (fun _ => queryTime) L ∧
        Eval (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) steps base selected ∧
        RowBoundary base (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (HashGreedyCode.initial shifts Q)
          (HashSelect.loopCap n F.length)) selected ∧
        (∀ i, (selected.stacks i).length ≤ L) ∧
        StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) (steps + 1) base
          (NativeLeafRun.roundsSpace base n F.length (SparseCode.distanceDenom F.length B) L K) := by
  obtain ⟨C, E, degree, Cs, es, cutoff, hC, hE, hdegree, hquery⟩ :=
    NativeHashQueries.marked k C0 d0 hk
  refine ⟨C, E, degree, Cs, es, cutoff, hC, hE, hdegree, ?_⟩
  intro n inputLength R hn hnI B F hv hm hmB shifts Q base hr hb hformula hamb hupper L hL
    queryTime K
  obtain ⟨hR, hrounds, hCwidth, hcounter, hbytes, href, hgrowth, _hnL⟩ :=
    NativeLeafRun.common_bounds (NativeLeafSemantics.indexed F) shifts Q R
  obtain ⟨steps, selected, ht, he, hselected, _h781, _h9, hbound, hs⟩ :=
    NativeLeafRun.ready_rounds (NativeLeafSemantics.indexed F) hm
      (HashGreedyCode.initial shifts Q) (SparseCode.distanceDenom F.length B) rfl
      (HighQueryProgram.marked k) (fun _ => queryTime) base hr L K
      (fun i => (hb i).trans hR) hrounds hcounter href hgrowth hCwidth hbytes (by
        intro rows word d _hrows hattained _hbytes hword hframe hhistory hcounter hscratch
          e tail a hready
        obtain ⟨rounds, hrounds, rfl⟩ := hattained
        let input := HashQueryEntry.recordState a tail (Encoding.encodeNat e.val)
        obtain ⟨t, out, he, ht, hcount, hws, hread, hreset, h324, hlen, _hp⟩ :=
          hquery n inputLength R hn hnI F hv hm hmB shifts Q rounds hrounds
            word base d a e tail (NativeHashQuerySetup.hiddenCap input)
            hr hb hformula hamb hL hupper hword hframe hhistory hcounter hscratch hready
            (NativeHashQuerySetup.hiddenCap_bound input)
        have hsrc : input.stacks 320 = tail := by
          simp [input, HashQueryEntry.recordState, RecordPrograms.state, HashMassAdapter.recordPorts]
        have hreset' : RecordPrograms.state HashMassAdapter.recordPorts out
            false true false tail [] = out :=
          (congrArg (fun word => RecordPrograms.state HashMassAdapter.recordPorts out
            false true false word []) hsrc.symm).trans hreset
        refine ⟨t, out, ?_, ?_, ?_, ?_, hlen, h324, ?_⟩
        · change t ≤ Nat.ceil (Statement.runtimeBound C E degree inputLength n)
          omega
        · exact hws.trans ((HashMassAdapter.workspace_recordState a false true false tail
            (Encoding.encodeNat e.val).reverse).trans hready.workspace_ready)
        · simpa [input, HashQueryEntry.recordState, RecordPrograms.state,
            HashMassAdapter.recordPorts, HashMassAdapter.read] using hread
        · rw [hcount, countWord_toNat]
        · rw [hreset']
          exact he) (by
        intro rows word d _hrows hattained _hbytes hword hframe hhistory hcounter hscratch hd
          e tail a t middle hready hread htail _hindex _hn hactual
        obtain ⟨rounds, hrounds, rfl⟩ := hattained
        obtain ⟨steps, out, he, _ht, _hcount, _hws, _hread, _hreset, _h324, _hlen, hp⟩ :=
          hquery n inputLength R hn hnI F hv hm hmB shifts Q rounds hrounds
            word base d a e tail (3 * L + 2)
            hr hb hformula hamb hL hupper hword hframe hhistory hcounter hscratch hready
            (HighQueryEntryShadow.record_hidden_bound d a F.length
              (SparseCode.distanceDenom F.length B) L word tail (Encoding.encodeNat e.val)
              hd hready hread htail)
        have ht := SubexpPrimeProgram.eval_steps_unique hactual he 778 777
        exact ⟨fun j z hj hz i => hp.bound j z (by omega) hz i⟩)
  exact ⟨steps, selected, ht, he, hselected, hbound, hs⟩


open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
/-- The fixed local program executes preparation, every staged greedy round
and the separate accepted-history query. All constants precede the original
input; storage is polynomial and the full canonical count retains ambient n. -/
theorem local_execution (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
    ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
      1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
      ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      ∀ (F : RawCNF n) (a : State 40 896), Valid k F → F ≠ [] → F.length ≤ n * B →
      (∀ i, (a.stacks i).length ≤ W) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
      a.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (a.stacks 785) = n →
      BinaryArithmetic.toNat (a.stacks 786) = B →
      ∃ steps ≤ Nat.ceil (Statement.runtimeBound Ct At timeDegree inputLength n), ∃ out,
        Eval (NativeLeafProgram.localCommand k) steps a out ∧
        out.stacks 788 = countWord (rawCount F) ∧
        ∀ t z, t ≤ steps → Trace (NativeLeafProgram.localProgram k) t
          (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
          ∀ i, (z.stacks i).length ≤ Cs * (inputLength + 1) ^ spaceDegree := by
  obtain ⟨C0, d0, Cp, Ap, dp, Np, hCp, hprepare⟩ :=
    prepared_loaded k parameterCoefficient parameterDegree
  obtain ⟨Cm, Em, dm, Csm, esm, Nm, hCm, hEm, hdm, hmarked⟩ := marked_rounds k C0 d0 hk
  obtain ⟨Ca, Ea, da, Csa, esa, Na, hCa, hEa, hda, haccepted⟩ :=
    NativeHashQueries.accepted k C0 d0 hk
  obtain ⟨Cr, Er, dr, Nr, hCr, hEr, hdr, hroundTime⟩ :=
    chosen_rounds_runtimeBound k C0 d0 Cm Em dm hCm hEm hdm
  obtain ⟨Cl, dl, hspace⟩ := chosen_loaded_local_space k parameterCoefficient parameterDegree
  obtain ⟨Ns, hschedule⟩ := Filter.eventually_atTop.mp
    (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1))
  let Ck := Csm + Csa + 3 * C0 + 2
  let dk := esm + esa + d0
  refine ⟨Ck + Cl, dk + dl, Cp + Cr + 2 * Ca + (61 * C0 + 71 : ℕ),
    (Ap : ℝ) + Er + Ea, dp + dr + da + d0,
    max (max (max Np Nm) (max Na Nr)) (max Ns 1), ?_, ?_, by omega, ?_⟩
  · have := Nat.cast_nonneg (α := ℝ) (61 * C0 + 71)
    linarith
  · have := Nat.cast_nonneg (α := ℝ) Ap
    linarith
  · intro n inputLength parameterBound hncut hnI hp B W F a hv hne hmB ha hempty hformula hn hBword
    have hnpos : 0 < n := by omega
    have hm : 0 < F.length := List.length_pos_iff.mpr hne
    have hB : 0 < B := by
      dsimp only [B]
      have hM := (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
      positivity
    obtain ⟨prepareSteps, started, prepared, base, shifts, Q, ep, tp, hstarted, hmetadata,
      hprepared, hr, hgood, hdistance, hbody, hamb, hbase, hupper, hL, sp⟩ :=
      hprepare n inputLength parameterBound (by omega) hnI hp F a hne hmB ha hempty hformula hn hBword
    let startup := W + NativeLeafSetup.canonicalStartTime n F.length W
    let R := NativeLeafPreparation.retainedBound F.length B startup started prepared
    let L := NativeLeafRun.commonBound n F.length B R
    let queryTime := Nat.ceil (Statement.runtimeBound Cm Em dm inputLength n)
    let K := Ck * (inputLength + 1) ^ dk
    have component (C d : ℕ) (hc : C ≤ Ck) (hd : d ≤ dk) :
        C * (inputLength + 1) ^ d ≤ K :=
      Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)
    have hLpower : L ≤ C0 * (inputLength + 1) ^ dk :=
      hL.trans (Nat.mul_le_mul_left C0 (Nat.pow_le_pow_right (by omega) (by dsimp [dk]; omega)))
    have hframeK : 3 * L + 2 ≤ K := by
      have hone : 1 ≤ (inputLength + 1) ^ dk := Nat.one_le_pow' _ _
      change 3 * L + 2 ≤ Ck * (inputLength + 1) ^ dk
      dsimp only [Ck]
      nlinarith only [hLpower, hone,
        Nat.zero_le ((Csm + Csa) * (inputLength + 1) ^ dk)]
    have hmarkedK : max (Csm * (inputLength + 1) ^ esm) (3 * L + 2) ≤ K :=
      max_le (component Csm esm (by dsimp [Ck]; omega) (by dsimp [dk]; omega)) hframeK
    have hacceptedK : max (Csa * (inputLength + 1) ^ esa) L ≤ K :=
      max_le (component Csa esa (by dsimp [Ck]; omega) (by dsimp [dk]; omega)) (by omega)
    obtain ⟨hR, _hloop, _hC, _hc, _hbytes, _href, _hgrowth, hnL⟩ :=
      NativeLeafRun.common_bounds (NativeLeafSemantics.indexed F) shifts Q R
    have hbaseL : ∀ i, (base.stacks i).length ≤ L := fun i => (hbase i).trans hR
    obtain ⟨roundSteps, selected, tr, er, hselected, hselectedBound, sr⟩ :=
      hmarked n inputLength R (by omega) hnI F hv hm hmB shifts Q base hr hbase hbody hamb hupper hL
    obtain ⟨querySteps, middle, eq, tq, hword, _hwordLength, sq⟩ :=
      haccepted n inputLength R (by omega) hnI F hv hm hmB shifts Q (HashSelect.loopCap n F.length)
        le_rfl base selected L hr hbase hbody hamb hL hupper hselected
        (fun i _ => AcceptedQueryStage.staged_bound selected L hselectedBound i)
    have sr' : StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k))
        (roundSteps + 1) base
        (NativeLeafRun.roundsSpace base n F.length (SparseCode.distanceDenom F.length B) L K) := by
      constructor
      intro t z ht hz i
      apply (sr.bound t z ht hz i).trans
      change max (max _ _) _ ≤ max (max K _) _
      exact max_le_max (max_le_max hmarkedK le_rfl) le_rfl
    have sq' : StageSpace (HighQueryProgram.accepted k) querySteps
        (AcceptedQueryStage.staged selected) K :=
      ⟨fun t z ht hz i => (sq.bound t z (by omega) hz i).trans hacceptedK⟩
    obtain ⟨steps, out, ht, he, _hout, hcount, _hbound, hprefix⟩ :=
      local_from_runs k F hm hB shifts Q hgood hdistance a base selected middle
        prepareSteps roundSteps querySteps L (C0 * (inputLength + 1) ^ d0)
        (NativeLeafRun.roundsSpace base n F.length (SparseCode.distanceDenom F.length B) L K) K
        ep sp hr hselected hselectedBound hnL er sr' eq hword sq'
    have tr' : (roundSteps : ℝ) ≤ Statement.runtimeBound Cr Er dr inputLength n :=
      (Nat.cast_le.mpr tr).trans (hroundTime n inputLength F.length R (by omega) hmB
        (HashGreedyCode.initial shifts Q) base hr hm (fun _ => queryTime) queryTime
        hbaseL hL (fun _ => le_rfl) le_rfl)
    have tt := local_time_runtimeBound (Cp := Cp) (Cr := Cr) (Cq := Ca)
      (Ap := (Ap : ℝ)) (Ar := Er) (Aq := Ea) dp dr da C0 d0 inputLength n
      prepareSteps roundSteps querySteps steps L (by linarith) (by linarith) hCa
      (Nat.cast_nonneg Ap) (by linarith) (by linarith) tp tr' (by omega) hL (by omega)
    have hs := hspace n inputLength F.length parameterBound K hnpos hm hnI
      (hschedule n (by omega)) hp hmB started prepared base hstarted hmetadata hprepared
      (by rw [CounterPrograms.value_eq_toNat]; exact hr.clauses) hbase
    have hfirst : C0 * (inputLength + 1) ^ d0 ≤ K :=
      component C0 d0 (by dsimp [Ck]; omega) (by dsimp [dk]; omega)
    have hfinal : max K (Cl * (inputLength + 1) ^ dl) ≤
        (Ck + Cl) * (inputLength + 1) ^ (dk + dl) := by
      apply max_le
      · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨steps, ?_, out, he, hcount, ?_⟩
    · exact Nat.cast_le.mp (tt.trans (Nat.le_ceil _))
    · intro t z htz hz i
      apply (hprefix t z (by omega) hz i).trans
      apply (max_le (hfirst.trans (Nat.le_max_left _ _))
        ((Nat.le_max_right _ _).trans hs)).trans hfinal

/-- Uniform counting contract for the fixed native leaf. The remaining
hypotheses concern only numerical caps chosen by the outer program. There
is no local execution, query evaluator, successful code or resource service
premise. -/
theorem uniform_contract (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
    ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
      1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
      ∀ n inputLength parameterBound bound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      ∀ threshold : List Bool,
      BinaryArithmetic.toNat threshold = SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) →
      Cs * (inputLength + 1) ^ spaceDegree ≤ bound →
      101 * SparseCountProgram.formulaBound n k + 103 ≤ bound → 5 * n + 6 ≤ bound →
      LeafContract (n := n) k threshold parameterBound (NativeLeafProgram.command k)
        (time n k (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At timeDegree inputLength n)) bound)
        bound := by
  obtain ⟨Cs, spaceDegree, Ct, At, timeDegree, cutoff, hCt, hAt, hdegree, hlocal⟩ :=
    local_execution k parameterCoefficient parameterDegree hk
  refine ⟨Cs, spaceDegree, Ct, At, timeDegree, cutoff, hCt, hAt, hdegree, ?_⟩
  intro n inputLength parameterBound bound hcut hnI hp threshold hthreshold hlocalBound hclassifier hpower
  apply contract_of_local_execution threshold (by omega) (by
    rw [hthreshold]
    exact (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1)
    hlocalBound hclassifier hpower
  intro F hv _hempty hne hmB a hformula hn hBword ha hempty _hregs
  exact hlocal n inputLength parameterBound hcut hnI hp F a hv hne
    (by simpa only [hthreshold] using hmB) ha hempty hformula hn
    (by simpa only [hthreshold] using hBword)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
