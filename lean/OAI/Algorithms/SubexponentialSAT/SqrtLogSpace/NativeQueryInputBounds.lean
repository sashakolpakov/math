import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryVisibleSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets

/-! Fixed input-length bounds for the literal trial and accepted query
preparations. The common bound is produced before the greedy loop; none of
these caps contains a suspended caller word or a repeated-node scratch cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry LeafParametersProgram CostAssembly.Polynomial
open NativeQueryPreparation ProducedQueryResources

/-- One source allowance covers the actual marked entry and both canonical
numeric and physical parameter words. All coefficients are fixed first. -/
def sourceCap (Cn dn Cl dl N L k : ℕ) : ℕ :=
  3 * L + 2 + Cn * (N + 1) ^ dn + Cl * (L + k + 1) ^ dl

/-- Both literal frontends fit this source-only cost. -/
def frontendCap (Cf df L k : ℕ) : ℕ :=
  10 * (L + 1) + Cf * (L + k + 1) ^ df + 12

/-- This is the actual Setup.localBound after the frontend and preparation,
with its fixed preparation coefficient and degree. -/
def preparedCap (Cp dp Cn dn Cl dl Cf df N L k : ℕ) : ℕ :=
  let A := sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k
  HighQuerySetup.localBound A (Cp * (A + 1) ^ dp)

/-- Canonical padding comes from the real frontend inputLengths definition;
the checked FrontState.canonicalLengths identifies these same words later. -/
theorem canonical_lengths_cubic : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k T : ℕ), q.Valid →
      LeafScopeInputBounds.capacity q k ≤ 106 * T ^ 3 →
      ∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ C * (T + 1) ^ d := by
  obtain ⟨C,d,h⟩ := Serialization.uniform_guarded_lengths_polynomial
  have hp : Ordinary (fun T => C *
      (LeafQueryFrontend.parameterSize (106 * T ^ 3) + 1) ^ d) := by
    obtain ⟨A,e,hA⟩ := LeafQueryFrontend.parameterSize_poly
    have hinner : Ordinary (fun T => A * (106 * T ^ 3 + 1) ^ e) :=
      ordinary_mul (ordinary_const A) (ordinary_pow
        (ordinary_add (ordinary_mul (ordinary_const 106) (ordinary_pow ordinary_id 3))
          (ordinary_const 1)) e)
    obtain ⟨D,f,hD⟩ := ordinary_mul (ordinary_const C)
      (ordinary_pow (ordinary_add hinner (ordinary_const 1)) d)
    refine ⟨D,f,?_⟩
    intro T
    exact (Nat.mul_le_mul_left C (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hA (106*T^3)) 1) d)).trans (hD T)
  obtain ⟨A,e,hA⟩ := hp
  refine ⟨A,e,?_⟩
  intro q k T hv hcap i
  have hcounts := LeafQueryFrontend.parameter_counts_bound q k hv
  have hlengths := LeafQueryFrontend.parameter_lengths_bound q k hv
  have hmono : LeafQueryFrontend.parameterSize (LeafScopeInputBounds.capacity q k) ≤
      LeafQueryFrontend.parameterSize (106*T^3) := by
    unfold LeafQueryFrontend.parameterSize LeafQueryFrontend.numericMajorant LeafQueryFrontend.conversionCost
    gcongr
  exact (h (q.input k) (q.inputLengths k) _ hcounts hlengths i).trans
    ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hmono 1) d)).trans (hA T))

/-- The common physical selector cap dominates its own scalar sum. -/
theorem scalar_le_common (n m B W : ℕ) :
    HashQueryInputBounds.commonCap n m B W ≤ NativeLeafRun.commonBound n m B W := by
  have h := Nat.le_self_pow (show 3 ≠ 0 by decide)
    (HashQueryInputBounds.commonCap n m B W)
  unfold NativeLeafRun.commonBound
  omega

private theorem sourceCap_mono (Cn dn Cl dl N k L U : ℕ) (h : L ≤ U) :
    sourceCap Cn dn Cl dl N L k ≤ sourceCap Cn dn Cl dl N U k := by
  unfold sourceCap
  gcongr

private theorem frontendCap_mono (Cf df k L U : ℕ) (h : L ≤ U) :
    frontendCap Cf df L k ≤ frontendCap Cf df U k := by
  unfold frontendCap
  gcongr

private theorem preparedCap_mono (Cp dp Cn dn Cl dl Cf df N k L U : ℕ) (h : L ≤ U) :
    preparedCap Cp dp Cn dn Cl dl Cf df N L k ≤
      preparedCap Cp dp Cn dn Cl dl Cf df N U k := by
  have hs := sourceCap_mono Cn dn Cl dl N k L U h
  have hf := frontendCap_mono Cf df k L U h
  dsimp only [preparedCap, HighQuerySetup.localBound]
  have ha := Nat.add_le_add hs hf
  exact Nat.add_le_add_right (Nat.add_le_add ha
    (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) dp))) 1

/-- Substitution uses a fixed polynomial for the genuinely produced common
bound. The degree is independent of all later states, candidates and nodes. -/
theorem cap_polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C d : ℕ, ∀ N L : ℕ, L ≤ C0 * (N + 1) ^ d0 →
      sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k +
        preparedCap Cp dp Cn dn Cl dl Cf df N L k + 4*N + 6 ≤ C * (N + 1) ^ d := by
  let U := fun N => C0 * (N+1)^d0
  have hU : Ordinary U := ordinary_mul (ordinary_const C0)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) d0)
  have hK := ordinary_add (ordinary_add hU (ordinary_const k)) (ordinary_const 1)
  have hS : Ordinary (fun N => sourceCap Cn dn Cl dl N (U N) k) :=
    ordinary_add (ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 3) hU) (ordinary_const 2))
      (ordinary_mul (ordinary_const Cn) (ordinary_pow
        (ordinary_add ordinary_id (ordinary_const 1)) dn)))
      (ordinary_mul (ordinary_const Cl) (ordinary_pow hK dl))
  have hF : Ordinary (fun N => frontendCap Cf df (U N) k) :=
    ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 10) (ordinary_add hU (ordinary_const 1)))
      (ordinary_mul (ordinary_const Cf) (ordinary_pow hK df))) (ordinary_const 12)
  have hA := ordinary_add hS hF
  have hP : Ordinary (fun N => preparedCap Cp dp Cn dn Cl dl Cf df N (U N) k) :=
    ordinary_add (ordinary_add hA (ordinary_mul (ordinary_const Cp)
      (ordinary_pow (ordinary_add hA (ordinary_const 1)) dp))) (ordinary_const 1)
  obtain ⟨C,d,hC⟩ := ordinary_add (ordinary_add (ordinary_add (ordinary_add hS hF) hP)
    (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)
  refine ⟨C,d,?_⟩
  intro N L hL
  have hs := sourceCap_mono Cn dn Cl dl N k L (U N) hL
  have hf := frontendCap_mono Cf df k L (U N) hL
  have hp := preparedCap_mono Cp dp Cn dn Cl dl Cf df N k L (U N) hL
  exact (by omega : sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k +
    preparedCap Cp dp Cn dn Cl dl Cf df N L k + 4*N+6 ≤
      sourceCap Cn dn Cl dl N (U N) k + frontendCap Cf df (U N) k +
        preparedCap Cp dp Cn dn Cl dl Cf df N (U N) k +4*N+6).trans (hC N)


/-- Literal losing or winning trial queries have one source cap before the
candidate, mark, retained collector and physical padding are chosen. -/
theorem trial_inputs (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (d a : State 40 896) (e : Fin F.length) (tail : List Bool),
      word.length = HashCandidates.payloadWidth F.length (SparseCode.distanceDenom F.length B) →
      (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ R) →
      d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      (d.stacks 783).length = HashCandidates.digitWidth F.length →
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) → d.stacks 767 = [] →
      HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
        (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
          (SparseCode.distanceDenom F.length B) word))) a →
      let q := trialQuery F hm shifts Q rounds word e d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      q.Valid ∧ ambient q = n ∧ 1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      (∀ j, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len j ≤ S) ∧
      HighMarkedFrontend.budget q k ≤ frontendCap Cf df L k ∧ 3*L+2 ≤ S := by
  obtain ⟨Cn,dn,cutoff,hnum⟩ := HashQueryParameterBounds.trial_numeric_caps k hk
  obtain ⟨Cl,dl,hlen⟩ := canonical_lengths_cubic
  obtain ⟨Cf,df,hfront⟩ := HashQueryParameterBounds.trial_frontend_budget
  refine ⟨Cn,dn,Cl,dl,Cf,df,max cutoff 1,?_⟩
  intro n N R hcut hinput B F hv hm hmb shifts Q rounds hr word d a e tail
    hword hmasters hformula hhistory hwidth hmod hamb hclean hscratch hready q L S
  have hn : 0 < n := by omega
  obtain ⟨hvq,hqn,_hscan,_hsmall,hnumpos,hnnum,hinum,hvalues⟩ :=
    hnum n N (by omega) hinput F hv hm hmb shifts Q rounds hr word e d hwidth hmod hamb
  obtain ⟨hcapacity,hcost⟩ := hfront n k B R F hn hm shifts Q rounds hr word d a e tail
    hword hmasters hformula hhistory hwidth hmod hamb hclean hscratch hready
  have hscalar := scalar_le_common n F.length B R
  have hbase : HashQueryInputBounds.commonCap n F.length B R+k+1 ≤ L+k+1 := by
    dsimp only [L]
    omega
  have hnS : Cn*(N+1)^dn ≤ S := by dsimp only [S,sourceCap]; omega
  have hlS : Cl*(L+k+1)^dl ≤ S := by dsimp only [S,sourceCap]; omega
  have hfrontcost : q.inputBudget k ≤ Cf*(L+k+1)^df :=
    hcost.trans (Nat.mul_le_mul_left Cf (Nat.pow_le_pow_left hbase df))
  have hindex : q.index.length ≤ L+1 := by
    change (Encoding.encodeNat e.val).length ≤ L+1
    rw [Encoding.length_encodeNat]
    have he := e.isLt
    unfold HashQueryInputBounds.commonCap at hscalar
    change _ ≤ L at hscalar
    omega
  refine ⟨hvq,hqn,hnumpos.trans hnS,hnnum.trans hnS,hinum.trans hnS,?_,?_,?_,?_⟩
  · intro padding j
    exact ⟨(hvalues padding j).1.trans hnS,(hvalues padding j).2.trans hnS⟩
  · intro j
    exact (hlen q k _ hvq hcapacity j).trans
      ((Nat.mul_le_mul_left Cl (Nat.pow_le_pow_left hbase dl)).trans hlS)
  · change 10*q.index.length+q.inputBudget k+12 ≤ frontendCap Cf df L k
    unfold frontendCap
    omega
  · dsimp only [S,sourceCap]
    omega

/-- The history-only final query uses the same kind of concrete source cap;
there is no candidate product and no unrestricted caller-word contribution. -/
theorem accepted_inputs (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ d : State 40 896,
      (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ R) →
      d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      (d.stacks 783).length = HashCandidates.digitWidth F.length →
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) →
      let q := acceptedQuery F hm shifts Q rounds d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      q.Valid ∧ ambient q = n ∧ 1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      (∀ j, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len j ≤ S) ∧
      HighMarkedFrontend.acceptedBudget q k ≤ frontendCap Cf df L k ∧ 3*L+2 ≤ S := by
  obtain ⟨Cn,dn,cutoff,hnum⟩ := HashQueryParameterBounds.accepted_numeric_caps k hk
  obtain ⟨Cl,dl,hlen⟩ := canonical_lengths_cubic
  obtain ⟨Cf,df,hfront⟩ := HashQueryParameterBounds.accepted_frontend_budget
  refine ⟨Cn,dn,Cl,dl,Cf,df,max cutoff 1,?_⟩
  intro n N R hcut hinput B F hv hm hmb shifts Q rounds hr d hmasters
    hformula hhistory hwidth hmod hamb hclean q L S
  have hn : 0 < n := by omega
  obtain ⟨hvq,hqn,_hscan,_hsmall,hnumpos,hnnum,hinum,hvalues⟩ :=
    hnum n N (by omega) hinput F hv hm hmb shifts Q rounds hr d hwidth hmod hamb
  obtain ⟨hcapacity,hcost⟩ := hfront n k B R F hn hm shifts Q rounds hr d
    hmasters hformula hhistory hwidth hmod hamb hclean
  have hscalar := scalar_le_common n F.length B R
  have hbase : HashQueryInputBounds.commonCap n F.length B R+k+1 ≤ L+k+1 := by
    dsimp only [L]
    omega
  have hnS : Cn*(N+1)^dn ≤ S := by dsimp only [S,sourceCap]; omega
  have hlS : Cl*(L+k+1)^dl ≤ S := by dsimp only [S,sourceCap]; omega
  have hfrontcost : q.inputBudget k ≤ Cf*(L+k+1)^df :=
    hcost.trans (Nat.mul_le_mul_left Cf (Nat.pow_le_pow_left hbase df))
  refine ⟨hvq,hqn,hnumpos.trans hnS,hnnum.trans hnS,hinum.trans hnS,?_,?_,?_,?_⟩
  · intro padding j
    exact ⟨(hvalues padding j).1.trans hnS,(hvalues padding j).2.trans hnS⟩
  · intro j
    exact (hlen q k _ hvq hcapacity j).trans
      ((Nat.mul_le_mul_left Cl (Nat.pow_le_pow_left hbase dl)).trans hlS)
  · change q.inputBudget k+5 ≤ frontendCap Cf df L k
    unfold frontendCap
    omega
  · dsimp only [S,sourceCap]
    omega


/-- Substitute the actual startup and metadata output into the same common
bound used by every staged round and the final accepted history. -/
theorem chosen_cap_polynomial
    (k wordCoefficient wordDegree Cp dp Cn dn Cl dl Cf df : ℕ) :
    ∃ C d : ℕ, ∀ n N m W : ℕ,
      0 < n → 0 < m → n ≤ N → 1 ≤ sparsifySchedule n →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      m ≤ n*B → W ≤ wordCoefficient*(N+1)^wordDegree →
      let startup := W+NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : State 40 896, (∀ i, (a.stacks i).length ≤ startup) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startup+NativeLeafSetup.parameterTime m B startup
        (a.stacks 782).length (a.stacks 786).length) →
      let R := NativeLeafPreparation.retainedBound m B startup a prepared
      let L := NativeLeafRun.commonBound n m B R
      sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k +
        preparedCap Cp dp Cn dn Cl dl Cf df N L k + 4*N+6 ≤ C*(N+1)^d := by
  obtain ⟨C0,d0,hcommon⟩ :=
    LeafPreparationBudgets.chosen_prepared_common_bound k wordCoefficient wordDegree
  obtain ⟨C,d,hcap⟩ := cap_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  refine ⟨C,d,?_⟩
  intro n N m W hn hm hN hschedule B hmb hW startup a prepared ha hmeta hp R L
  have h := hcommon n N m W hn hm hN hschedule hmb hW a prepared ha hmeta hp
  exact hcap N L ((Nat.le_max_right _ _).trans h)

/-- Actual Setup uses a smaller frontend cost than the uniform literal-query
allowance, so its retained local bound fits the same preparedCap. -/
theorem setup_local_bound_le (Cp dp Cn dn Cl dl Cf df N L k f : ℕ)
    (hf : f ≤ frontendCap Cf df L k) :
    HighQuerySetup.localBound (sourceCap Cn dn Cl dl N L k+f)
      (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp) ≤
        preparedCap Cp dp Cn dn Cl dl Cf df N L k := by
  dsimp only [HighQuerySetup.localBound, preparedCap]
  gcongr

/-- The actual source-prefix bound is a maximum with the carried frame;
its local polynomial has no hidden-word or repeated-node scratch term. -/
theorem setup_prefix_bound_le (q : LeafQueryFrontend.Query)
    (Cp dp Cn dn Cl dl Cf df N L k f B : ℕ)
    (hf : f ≤ frontendCap Cf df L k) (hn : BinaryArithmetic.toNat q.ambient ≤ N) :
    HighQuerySetup.prefixBound q (sourceCap Cn dn Cl dl N L k+f)
      (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp) B ≤
        max (12*preparedCap Cp dp Cn dn Cl dl Cf df N L k+4*N+6) B := by
  have hp := setup_local_bound_le Cp dp Cn dn Cl dl Cf df N L k f hf
  unfold HighQuerySetup.prefixBound HighQuerySetup.boundaryBound
  omega

/-- The measured frontend/preparation/seed cost uses the same actual
local bound; it never uses the collector's physical length. -/
theorem setup_time_le (Cp dp Cn dn Cl dl Cf df N L k f : ℕ)
    (hf : f ≤ frontendCap Cf df L k) :
    f + Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp +
      110*HighQuerySetup.localBound (sourceCap Cn dn Cl dl N L k+f)
        (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp)+81 ≤
      frontendCap Cf df L k+111*preparedCap Cp dp Cn dn Cl dl Cf df N L k+81 := by
  have hp := setup_local_bound_le Cp dp Cn dn Cl dl Cf df N L k f hf
  have hc : Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp ≤
      preparedCap Cp dp Cn dn Cl dl Cf df N L k := by
    have h := Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left
      (show sourceCap Cn dn Cl dl N L k+f+1 ≤
        sourceCap Cn dn Cl dl N L k+frontendCap Cf df L k+1 by omega) dp)
    dsimp only [preparedCap,HighQuerySetup.localBound]
    omega
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
