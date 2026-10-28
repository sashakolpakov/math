import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStep
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsMatrix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsTuples
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerResourcesTable

namespace OAI.Algorithms

/-! A fixed polynomial bound for the actual head callback. The matrix output
is bounded using its native execution witness, not an assumed output oracle.
The resource Z includes the current tuple payload and the separately bounded
all-row matrix envelope. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem ite_word_bound (P : Prop) [Decidable P] (x y : List Bool) (M : ℕ)
    (hx : x.length ≤ M) (hy : y.length ≤ M) : (if P then x else y).length ≤ M := by
  split <;> assumption

 theorem matrix_base_bound (a : Data) (M : ℕ) (ha : WordBound M a) :
    ∀ i, (matrixBase a i).length ≤ M := by
  intro i
  unfold matrixBase
  repeat' first
    | apply ite_word_bound
    | exact ha _
    | exact Nat.zero_le M

 theorem matrix_initial_bound (a : Data) (regs : Fin 16 → Bool) (D M : ℕ)
    (ha : WordBound M a) (hD : D ≤ M) :
    WordBound M (LayoutMatrixProgram.initialState (matrixBase a) regs D) := by
  intro i
  dsimp only [LayoutMatrixProgram.initialState,LayoutMatrixProgram.state]
  split_ifs <;> try simp only [List.length_nil,List.length_replicate]
  all_goals first | exact matrix_base_bound a M ha i | exact hD | exact Nat.zero_le M

 theorem actual_bucket_bytes_le (W : List Bool) (T B D n : ℕ) (js : List ℕ)
    (rows : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows shifted)
    (hjs : ∀ v∈js,v < n) :
    (BucketTupleProgram.Table.tableBits (BucketTupleProgram.actualBuckets W shifted js n js.length)).length
      ≤ matrixEnvelope W T B D n js.length := by
  rw [BucketTupleProgram.actualBuckets_bytes]
  have hb := BucketProgram.Controller.Resources.tableOutput_length_le_cost W shifted js n js.length
  have hc := matrix_native_cost W T B D n js rows shifted Rel hr hy hjs
  omega

 theorem selected_context_length (n N : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (selectedContext n N rows z).length ≤ 5*(preparationSize n N rows low W z)^2 := by
  let s := preparationSize n N rows low W z
  have h := factor_local_bound n N rows W z s
    (by dsimp [s,preparationSize]; omega) (by dsimp [s,preparationSize]; omega)
    (by dsimp [s,preparationSize]; omega) (by dsimp [s,preparationSize]; omega)
    (by dsimp [s,preparationSize]; omega) (by dsimp [s,preparationSize]; omega)
  exact h 0

 theorem selected_mask_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedMask n rows low z).length=n :=
  HeadScatterProgram.mask_length _ _ _ (HeadIdentifierProgram.chosenIds_bound _ _)

 theorem headStep_cost_le (entry : Cmd 16 256) (a : Data) (rp : Fin 8 → Bool)
    (mb : State 16 288) (rt : Fin 10 → Bool)
    (n N D W z T B A Z : ℕ) (rows prior : List (List Bool)) (low : List Bool)
    (matrixRows : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D (selectedHeads n rows low z) matrixRows)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) matrixRows shifted)
    (he : MatrixExecution entry (preparedHead a rp n N rows low W z) D n
      (selectedHeads n rows low z) T B matrixRows shifted mb)
    (ha : WordBound A a) (hsize : n ≤ rows.length)
    (hprep : A+5*(preparationSize n N rows low W z)^2 ≤ Z)
    (hs : preparationSize n N rows low W z ≤ Z) (hD : D ≤ Z)
    (hE : matrixEnvelope (a.stacks 141) T B D n (selectedHeads n rows low z).length ≤ Z)
    (hw : ∀ row∈prior,row.length ≤ Z) (hc : prior.length ≤ Z) :
    headStepCost a rp mb rt n N D W z T B rows prior low matrixRows shifted ≤
      100000000*(Z+1)^4 := by
  let s := preparationSize n N rows low W z
  let js := selectedHeads n rows low z
  let p := preparedHead a rp n N rows low W z
  have hEjs : matrixEnvelope (a.stacks 141) T B D n js.length ≤ Z := hE
  let bs := BucketTupleProgram.actualBuckets (a.stacks 141) shifted js n js.length
  let m := returned id (by decide) matrixInputs matrixOutputs p mb
  let q := tupleResult m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs
  have hjs : ∀ v∈js,v < n := HeadIdentifierProgram.chosenIds_bound _ _
  have p141 : p.stacks 141=a.stacks 141 := preparedHead_frame a rp n N rows low W z
    141 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp0 := prepareHead_bound a rp n N rows low W z A ha hsize
  have hp : WordBound Z p := wordBound_mono hp0.1 hprep
  have hy' : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (p.stacks 141))) matrixRows shifted := by
    simpa only [p141] using hy
  have hmb0 := matrix_post_wordBound entry p D n T B Z js matrixRows shifted mb Rel hr hy' hjs
    (matrix_initial_bound p _ D Z hp hD) he
  have hmb : WordBound (2*Z) mb := wordBound_mono hmb0 (by rw [p141]; omega)
  have hp' : WordBound (2*Z) p := wordBound_mono hp (by omega)
  have hm : WordBound (2*Z) m := returned_wordBound id (by decide) matrixInputs matrixOutputs p mb
    (2*Z) matrixInputs_protected matrixOutputs_protected (by decide) (by decide) hp' hmb
  have hn : n ≤ Z := by
    have hns : n ≤ s := by dsimp [s,preparationSize]; omega
    exact hns.trans hs
  have hmask : (selectedMask n rows low z).length ≤ 2*Z := by rw [selected_mask_length]; omega
  have hctx : (selectedContext n N rows z).length ≤ 2*Z := by
    have h := selected_context_length n N rows low W z
    omega
  have hbs : (BucketTupleProgram.Table.tableBits bs).length ≤ 2*Z :=
    (actual_bucket_bytes_le (a.stacks 141) T B D n js matrixRows shifted Rel hr hy hjs).trans (by omega)
  have ht := tuple_stage_bound m rt prior (selectedMask n rows low z) (selectedContext n N rows z)
    bs (2*Z) hm (fun row hx => (hw row hx).trans (by omega)) (hc.trans (by omega)) hmask hctx hbs
  have hclear := clearManyCost_le ([650,651,652,669,670,671] : List (Fin 768)) q
    (50*(2*Z+1)^3) ht.1
  have hstage := stageCost_linear id (by decide) matrixInputs matrixOutputs p mb
    (LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost (a.stacks 141) matrixRows+
      BucketProgram.Controller.cost (a.stacks 141) shifted js n js.length+3)
    (2*Z) matrixInputs_protected matrixOutputs_protected (by decide) (by decide) hp' hmb
  have hnative := matrix_native_cost (a.stacks 141) T B D n js matrixRows shifted Rel hr hy hjs
  have hnative' : LayoutMatrixProgram.commandCost T B D n js+
      BucketProgram.preMatrixCost (a.stacks 141) matrixRows+
      BucketProgram.Controller.cost (a.stacks 141) shifted js n js.length+3 ≤ Z := hnative.trans hEjs
  have hA : A ≤ Z := by omega
  have hs3 : s^3 ≤ (Z+1)^3 := by gcongr; omega
  have hZ : Z ≤ (Z+1)^3 := by nlinarith only [Nat.zero_le Z,Nat.zero_le (Z^2),Nat.zero_le (Z^3)]
  have hone : 1 ≤ (Z+1)^4 := one_le_pow₀ (by omega)
  have h34 : (Z+1)^3 ≤ (Z+1)^4 := pow_le_pow_right₀ (by omega) (by decide)
  have h24 : 2*Z+1 ≤ 3*(Z+1)^4 := by nlinarith only [hZ,h34,hone]
  have hpow3 : (2*Z+1)^3 ≤ 8*(Z+1)^3 := by calc
    _ ≤ (2*(Z+1))^3 := by gcongr; omega
    _ = _ := by ring
  have hpow4 : (2*Z+1)^4 ≤ 16*(Z+1)^4 := by calc
    _ ≤ (2*(Z+1))^4 := by gcongr; omega
    _ = _ := by ring
  norm_num [matrixInputs,matrixOutputs] at hstage
  norm_num only [List.length_cons,List.length_nil] at hclear
  have hstage' : stageCost id (by decide) matrixInputs matrixOutputs p mb
      (LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost (a.stacks 141) matrixRows+
        BucketProgram.Controller.cost (a.stacks 141) shifted js n js.length+3) ≤
      LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost (a.stacks 141) matrixRows+
        BucketProgram.Controller.cost (a.stacks 141) shifted js n js.length+3+1878*(2*Z+1) := hstage
  change prepareHeadCost a rp n N rows low W z+
    stageCost id (by decide) matrixInputs matrixOutputs p mb
      (LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost (a.stacks 141) matrixRows+
        BucketProgram.Controller.cost (a.stacks 141) shifted js n js.length+3)+
    tupleCost m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs+
    clearManyCost [650,651,652,669,670,671] q+2 ≤ _
  have hpCost : prepareHeadCost a rp n N rows low W z ≤ 100000*(A+s^3+1) := hp0.2
  have htCost : tupleCost m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs ≤
    3000000*(2*Z+1)^4 := ht.2
  nlinarith only [hpCost,hstage',hnative',htCost,hclear,hA,hs3,hZ,hone,h34,h24,hpow3,hpow4]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
