import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeAssemblyBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ResourceBudgets

/-! Numerical resources of the actual full leaf-preparation command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
open SqrtLog SqrtLog.LeafOuterProgram NativeLeafPreparation NativeCodeAssembly
open CodeAssemblyBudgets CodeSearchNativeBudgets

/-- The saved initial words and the produced metadata bound the actual
search-and-serialization phase without any search-count factor in space. -/
theorem metadata_code_bounds {m B A : ℕ} (prepared : Data)
    (hmeta : Metadata m B prepared) (ha : ∀ i, (prepared.stacks i).length ≤ A)
    (mword width : List Bool) (hmword : mword.length ≤ A) (hwidth : width.length ≤ A) :
    afterBoundary A m B (prepared.stacks 801) mword width ≤ 10000000000000000 * A ^ 5 ∧
    afterSpace A m B (prepared.stacks 800).length (prepared.stacks 801) mword width ≤
      20000000000000000 * A ^ 5 := by
  have hA := metadata_bound_pos prepared hmeta ha
  have hD := metadata_value_bound prepared hmeta ha 0
  have ht := metadata_value_bound prepared hmeta ha 1
  have hl := metadata_value_bound prepared hmeta ha 2
  have hd := metadata_value_bound prepared hmeta ha 3
  have hr := metadata_value_bound prepared hmeta ha 4
  have hg := metadata_value_bound prepared hmeta ha 5
  have hv := metadata_value_bound prepared hmeta ha 6
  change SparseCode.degree m B ≤ A at hD
  change SparseCode.localRows m B ≤ A at ht
  change SparseCode.localRows m B * SparseCode.degree m B ≤ A at hl
  change SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ A at hd
  change SparseCode.dimension m B ≤ A at hr
  change SparseCode.dimension m B * SparseCode.degree m B ≤ A at hg
  rw [Nat.mul_comm] at hg
  change 2 ^ SparseCode.dimension m B ≤ A at hv
  have hs := searchesSpace_le A m B (prepared.stacks 800).length (prepared.stacks 801).length
    hA hD ht hd hr (ha 800) (ha 801) hg hl
  have hb := afterBoundary_le A m B (prepared.stacks 801) mword width
    hA hr hD ht (ha 801) hmword hwidth hv hg hl
  have hp : A ^ 2 ≤ A ^ 5 := Nat.pow_le_pow_right hA (by decide)
  refine ⟨hb, ?_⟩
  unfold afterSpace
  exact max_le (hs.trans (Nat.mul_le_mul_left _ hp)) (by omega)

/-- The paid final clearing and zero-candidate constructor have fixed
bilinear cost in the actual depth and current physical word cap. -/
theorem finishTime_le (depth R : ℕ) :
    R + finishTime depth R ≤ 1000 * (depth + 1) * (R + 1) := by
  unfold finishTime
  nlinarith

/-- Space and retained output of preparation are bounded together by one
fixed sixth-degree polynomial. The exact depth is charged by value because
its zero candidate is physically materialized. -/
theorem continuation_bounds (m B L : ℕ) (a prepared : Data)
    (ha : ∀ i, (a.stacks i).length ≤ L) (hmeta : Metadata m B prepared)
    (hp : ∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length) :
    let A := L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length
    let Z := A + m + SparseCode.distanceDenom m B + 1
    max (L + 1) (continuationSpace m B L a prepared) ≤
      20000000000000000000 * Z ^ 6 ∧
    retainedBound m B L a prepared ≤ 20000000000000000000 * Z ^ 6 := by
  intro A Z
  have hLA : L ≤ A := by dsimp [A]; omega
  have hc := metadata_code_bounds prepared hmeta hp (a.stacks 782) (a.stacks 768)
    ((ha 782).trans hLA) ((ha 768).trans hLA)
  let R := afterBoundary A m B (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  have hR : R ≤ 10000000000000000 * Z ^ 5 := hc.1.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [Z]; omega) 5))
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hA : A + 1 ≤ Z := by dsimp [Z]; omega
  have hm : m ≤ Z := by dsimp [Z]; omega
  have hd : SparseCode.distanceDenom m B + 1 ≤ Z := by dsimp [Z]; omega
  have h56 : Z ^ 5 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by decide)
  have h16 : Z ≤ Z ^ 6 := Nat.le_self_pow (by decide) Z
  have h26 : Z ^ 2 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : 1 ≤ Z ^ 5 := Nat.one_le_pow' _ _
  have hR1 : R + 1 ≤ 10000000000000001 * Z ^ 5 := by omega
  have hf := (finishTime_le (SparseCode.distanceDenom m B) R).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hd) hR1)
  have hf' : R + finishTime (SparseCode.distanceDenom m B) R ≤
      20000000000000000000 * Z ^ 6 := by nlinarith only [hf]
  have hspace : afterSpace A m B (prepared.stacks 800).length
      (prepared.stacks 801) (a.stacks 782) (a.stacks 768) ≤
        20000000000000000000 * Z ^ 6 := by
    have h := hc.2.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (show A ≤ Z by omega) 5))
    nlinarith only [h, h56]
  have hlinear : A + 1 ≤ 20000000000000000000 * Z ^ 6 := by nlinarith only [hA, h16]
  have hw : HashCandidates.digitWidth m ≤ 3 * m + 1 := DyadicWidth.width_le_succ _
  have hw' : HashCandidates.digitWidth m ≤ 4 * Z := by omega
  have hprod := Nat.mul_le_mul (show SparseCode.distanceDenom m B ≤ Z by omega) hw'
  have hretained : 2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3 ≤
      20000000000000000000 * Z ^ 6 := by nlinarith only [hprod, h26, hZ, h16]
  constructor
  · change max (L + 1) (max (max (A + 1) _) (R + finishTime _ R)) ≤ _
    exact max_le (by omega) (max_le (max_le hlinear hspace) hf')
  · change max R _ ≤ _
    exact max_le (by nlinarith only [hR, h56]) hretained

/-- Startup, metadata production, both searches, serialization, final setup
and the retained initial history share one ordinary input-polynomial space
bound. Constants and degree are fixed before all runtime inputs. -/
theorem full_space_polynomial :
    ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < m → 0 < B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (L + 1) (continuationSpace m B L a prepared) ≤
        C * (n + m + W + SparseCode.distanceDenom m B + 16) ^ degree ∧
      retainedBound m B L a prepared ≤
        C * (n + m + W + SparseCode.distanceDenom m B + 16) ^ degree := by
  obtain ⟨C, degree, hparameter⟩ := NativeLeafSetup.canonicalParameterTime_polynomial
  refine ⟨20000000000000000000 * (C + 1) ^ 6, (degree + 1) * 6, ?_⟩
  intro n m B W hm hB L a prepared ha hmeta hp
  let A := L + NativeLeafSetup.parameterTime m B L
    (a.stacks 782).length (a.stacks 786).length
  let X := n + m + W + SparseCode.distanceDenom m B + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA : A + 1 ≤ C * X ^ degree :=
    (hparameter n m B W _ _ hm hB (ha 782) (ha 786)).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by dsimp [X]; omega) degree))
  have hexp : X ^ degree ≤ X ^ (degree + 1) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : X ≤ X ^ (degree + 1) := by
    simpa using Nat.pow_le_pow_right hX (by omega : 1 ≤ degree + 1)
  have hZ : A + m + SparseCode.distanceDenom m B + 1 ≤ (C + 1) * X ^ (degree + 1) := by
    have h := hA.trans (Nat.mul_le_mul_left C hexp)
    have hrest : m + SparseCode.distanceDenom m B ≤ X := by dsimp [X]; omega
    nlinarith only [h, hlinear, hrest]
  have hc := continuation_bounds m B L a prepared ha hmeta hp
  have hbound := Nat.mul_le_mul_left 20000000000000000000 (Nat.pow_le_pow_left hZ 6)
  have heq : 20000000000000000000 * ((C + 1) * X ^ (degree + 1)) ^ 6 =
      (20000000000000000000 * (C + 1) ^ 6) * X ^ ((degree + 1) * 6) := by
    rw [mul_pow, ← pow_mul, Nat.mul_assoc]
  rw [heq] at hbound
  exact ⟨hc.1.trans hbound, hc.2.trans hbound⟩

/-- The physically expanded selector depth is polynomial in its actual
numeric parameters; its binary word length alone would not suffice. -/
theorem distanceDenom_polynomial (m B : ℕ) :
    SparseCode.distanceDenom m B ≤ 20000 * (B + m + 1) ^ 4 := by
  have hl : SparseCode.logSize m ≤ m + 1 := by
    unfold SparseCode.logSize
    exact Nat.add_le_add_right (Nat.log_le_self 2 m) 1
  have hB : B ≤ B + m + 1 := by omega
  have hlog : SparseCode.logSize m ≤ B + m + 1 := by omega
  have h := Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) (Nat.pow_le_pow_left hlog 2)
  unfold SparseCode.distanceDenom
  nlinarith only [h]

/-- Eliminating the explicit depth leaves one polynomial in the actual
numeric occurrence, clause count, ambient size and incoming word bound. -/
theorem full_space_scalar_polynomial :
    ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < m → 0 < B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (L + 1) (continuationSpace m B L a prepared) ≤
        C * (n + m + B + W + 16) ^ degree ∧
      retainedBound m B L a prepared ≤ C * (n + m + B + W + 16) ^ degree := by
  obtain ⟨C, degree, hfull⟩ := full_space_polynomial
  refine ⟨C * 20001 ^ degree, 4 * degree, ?_⟩
  intro n m B W hm hB L a prepared ha hmeta hp
  let X := n + m + B + W + 16
  have hx : B + m + 1 ≤ X := by dsimp [X]; omega
  have hdepth := (distanceDenom_polynomial m B).trans
    (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hx 4))
  have hlin : n + m + W + 16 ≤ X ^ 4 :=
    (show n + m + W + 16 ≤ X by dsimp [X]; omega).trans
      (Nat.le_self_pow (by decide) X)
  have hsize : n + m + W + SparseCode.distanceDenom m B + 16 ≤ 20001 * X ^ 4 := by
    omega
  have h := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize degree)
  rw [mul_pow, ← pow_mul, ← Nat.mul_assoc] at h
  have hf := hfull n m B W hm hB a prepared ha hmeta hp
  exact ⟨hf.1.trans h, hf.2.trans h⟩

open SqrtLog.CodeSetupCost in
/-- The paid whole continuation is a fixed sixth power of the original
complete code envelope plus the actual physical boundary and scalar depth. -/
theorem continuationTime_le_envelope (m B L H wordCap : ℕ) (a prepared : Data)
    (ha : ∀ i, (a.stacks i).length ≤ L) (hmeta : Metadata m B prepared)
    (hp : ∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length)
    (ht : SparseCode.localRows m B ≤ H) (hD : SparseCode.degree m B ≤ H)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H)
    (hr : SparseCode.dimension m B ≤ H)
    (hq : (prepared.stacks 800).length ≤ wordCap)
    (hDl : (prepared.stacks 801).length ≤ wordCap) :
    let A := L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length
    continuationTime m B L a prepared ≤
      30000000000000000000 *
        (A + SparseCode.distanceDenom m B + envelope 3000000000000 H wordCap + 1) ^ 6 := by
  intro A
  have hLA : L ≤ A := by dsimp [A]; omega
  have hA := metadata_bound_pos prepared hmeta hp
  have hDA := metadata_value_bound prepared hmeta hp 0
  have htA := metadata_value_bound prepared hmeta hp 1
  have hl := metadata_value_bound prepared hmeta hp 2
  have hrA := metadata_value_bound prepared hmeta hp 4
  have hg := metadata_value_bound prepared hmeta hp 5
  have hv := metadata_value_bound prepared hmeta hp 6
  change SparseCode.degree m B ≤ A at hDA
  change SparseCode.localRows m B ≤ A at htA
  change SparseCode.localRows m B * SparseCode.degree m B ≤ A at hl
  change SparseCode.dimension m B ≤ A at hrA
  change SparseCode.dimension m B * SparseCode.degree m B ≤ A at hg
  rw [Nat.mul_comm] at hg
  change 2 ^ SparseCode.dimension m B ≤ A at hv
  have hmword : (a.stacks 782).length ≤ A := (ha 782).trans hLA
  have hwidth : (a.stacks 768).length ≤ A := (ha 768).trans hLA
  have htime := afterTime_le_envelope A m B (prepared.stacks 800).length H wordCap
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768) hA hrA hDA htA
    (hp 801) hmword hwidth hv hg hl ht hD hd hr hq hDl
  have hb := (metadata_code_bounds prepared hmeta hp (a.stacks 782) (a.stacks 768)
    hmword hwidth).1
  let R := afterBoundary A m B (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  let X := A + SparseCode.distanceDenom m B + envelope 3000000000000 H wordCap + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h56 : X ^ 5 ≤ X ^ 6 := Nat.pow_le_pow_right hX (by decide)
  have h16 : X ≤ X ^ 6 := Nat.le_self_pow (by decide) X
  have h1 : 1 ≤ X ^ 5 := Nat.one_le_pow' _ _
  have hP : NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length ≤ X := by
    dsimp [X, A]
    omega
  have hdepth : SparseCode.distanceDenom m B + 1 ≤ X := by dsimp [X]; omega
  have hR : R ≤ 10000000000000000 * X ^ 5 := hb.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [X]; omega) 5))
  have hR1 : R + 1 ≤ 10000000000000001 * X ^ 5 := by omega
  have hf := (finishTime_le (SparseCode.distanceDenom m B) R).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hdepth) hR1)
  have htime' := htime.trans (Nat.mul_le_mul_left 20000000000000000
    (Nat.pow_le_pow_left (show A + envelope 3000000000000 H wordCap + 1 ≤ X by
      dsimp [X]; omega) 5))
  change _ ≤ 30000000000000000000 * X ^ 6
  unfold continuationTime
  change NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length +
    afterTime A m B (prepared.stacks 800).length (prepared.stacks 801)
      (a.stacks 782) (a.stacks 768) + finishTime (SparseCode.distanceDenom m B) R ≤ _
  nlinarith only [hP, htime', hf, h56, h16]

/-- Actual greedy scalar and physical master-word cap, with no execution-time term. -/
theorem greedy_scalar_sum_le (n m B W : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hB : 0 < B) (hmb : m ≤ n * B) :
    n + m + SparseCode.totalRows m B + SparseCode.degreeBound m B +
      SparseCode.distanceDenom m B + HashCandidates.digitWidth m +
      HashSelect.loopCap n m + W + 1 ≤
        1000000 * (n + m + B + W + 16) ^ 5 := by
  let S := n + m + B + W + 16
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hrows := SparseCode.totalRows_le hn hm hB hmb
  have hlog : SparseCode.logSize m ≤ S := by
    have h := Nat.log_le_self 2 m
    dsimp [SparseCode.logSize, S]
    omega
  have hBS : B ≤ S := by dsimp [S]; omega
  have hdegree : SparseCode.degreeBound m B ≤ 320000 * S ^ 5 := by
    have hh := Nat.mul_le_mul (Nat.pow_le_pow_left hBS 2) (Nat.pow_le_pow_left hlog 3)
    have he : SparseCode.degreeBound m B = 320000 * (B ^ 2 * SparseCode.logSize m ^ 3) := by
      unfold SparseCode.degreeBound SparseCode.gapDenom
      ring
    rw [he]
    calc
      _ ≤ 320000 * (S ^ 2 * S ^ 3) := Nat.mul_le_mul_left _ hh
      _ = _ := by ring
  have hdepth : SparseCode.distanceDenom m B ≤ 20000 * S ^ 5 := by
    apply (distanceDenom_polynomial m B).trans
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (show B + m + 1 ≤ S by dsimp [S]; omega) 4).trans
      (Nat.pow_le_pow_right hS (by decide))
  have hwidth : HashCandidates.digitWidth m ≤ 3 * m + 1 := DyadicWidth.width_le_succ _
  have hsize : Nat.size m ≤ m := Nat.size_le.mpr (Nat.lt_pow_self (by decide))
  have hrounds : HashSelect.loopCap n m ≤ 2 * (n + m + 1) := by
    unfold HashSelect.loopCap
    omega
  have hsmall : n + m + SparseCode.totalRows m B + HashCandidates.digitWidth m +
      HashSelect.loopCap n m + W + 1 ≤ 6 * S := by
    dsimp [S]
    omega
  have hpow : S ≤ S ^ 5 := Nat.le_self_pow (by decide) S
  change _ ≤ 1000000 * S ^ 5
  omega

/-- The actual preparation output determines a common cap before any greedy
round. Both preparation prefixes and this cap are ordinary fixed polynomials. -/
theorem prepared_common_bound_polynomial :
    ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < n → 0 < m → 0 < B → m ≤ n * B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) ≤
          C * (n + m + B + W + 16) ^ degree := by
  obtain ⟨C, d, hprep⟩ := full_space_scalar_polynomial
  let K := 16 * 1000000 ^ 3 * (C + 1) ^ 15
  refine ⟨K + C, (d + 1) * 15, ?_⟩
  intro n m B W hn hm hB hmb L a prepared ha hmeta hp
  let X := n + m + B + W + 16
  let R := retainedBound m B L a prepared
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hh := hprep n m B W hm hB a prepared ha hmeta hp
  have hr : R ≤ C * X ^ d := hh.2
  have hlin : X ≤ X ^ (d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ d + 1 by omega)
  have hdpow : X ^ d ≤ X ^ (d + 1) := Nat.pow_le_pow_right hX (by omega)
  have hsize : n + m + B + R + 16 ≤ (C + 1) * X ^ (d + 1) := by
    have hr' := hr.trans (Nat.mul_le_mul_left C hdpow)
    have hrest : n + m + B + 16 ≤ X := by dsimp [X]; omega
    nlinarith only [hr', hlin, hrest]
  have hcap : HashQueryInputBounds.commonCap n m B R ≤
      1000000 * ((C + 1) * X ^ (d + 1)) ^ 5 :=
    (greedy_scalar_sum_le n m B R hn hm hB hmb).trans
      (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hsize 5))
  have hcommon := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hcap 3)
  have heq : 16 * (1000000 * ((C + 1) * X ^ (d + 1)) ^ 5) ^ 3 =
      K * X ^ ((d + 1) * 15) := by
    dsimp [K]
    simp only [mul_pow, ← pow_mul, Nat.reduceMul, Nat.mul_assoc]
    norm_num only [Nat.reducePow, Nat.reduceMul, ← Nat.mul_assoc]
  rw [heq] at hcommon
  have he : d ≤ (d + 1) * 15 := by omega
  have hprepare := hh.1.trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX he))
  apply max_le
  · exact hprepare.trans (Nat.mul_le_mul_right _ (by dsimp [K]; omega))
  · exact hcommon.trans (Nat.mul_le_mul_right _ (by omega))


/-- The actual disjoint choice and loaded input-word cap fix one polynomial
common selector boundary in original input length before all leaf calls. -/
theorem chosen_prepared_common_bound (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) ≤
          C * (inputLength + 1) ^ degree := by
  obtain ⟨C, degree, hprep⟩ := prepared_common_bound_polynomial
  obtain ⟨K, exponent, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  refine ⟨C * K ^ degree, exponent * degree, ?_⟩
  intro n inputLength m W hn hm hinput hs B hmb hW L a prepared ha hmeta hp
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  have h := hprep n m B W hn hm hB hmb a prepared ha hmeta hp
  have hcap := hsize n inputLength m W hinput hs hmb hW
  apply h.trans
  have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hcap degree)
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hh


theorem common_rounds_space_le (base : StructuredCalls.State 40 896) (n m B W K : ℕ)
    (hm : CounterPrograms.value (base.stacks 782) = m)
    (ha : ∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B W) :
    NativeLeafRun.roundsSpace base n m (SparseCode.distanceDenom m B)
      (NativeLeafRun.commonBound n m B W) K ≤
      max K (1000000 * (m + SparseCode.distanceDenom m B + NativeLeafRun.commonBound n m B W + 1) ^ 3) := by
  let S := HashQueryInputBounds.commonCap n m B W
  obtain ⟨hS, _, _, hd, hw, hb, _⟩ := HashQueryInputBounds.commonCap_bounds n m B W
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have hp : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hd hw
  exact HashGreedyBudgets.staged_rounds_space_le base n m (SparseCode.distanceDenom m B)
    (NativeLeafRun.commonBound n m B W) K hm ha
    (by change _ ≤ 16 * S ^ 3; omega) (by change _ ≤ 16 * S ^ 3; omega)

/-- The actual produced preparation boundary and full streamed selector
share a fixed input polynomial, with the independent query prefix cap kept
separate from its running time. -/
theorem prepared_selector_space_polynomial :
    ∃ C degree : ℕ, ∀ n m B W K : ℕ, 0 < n → 0 < m → 0 < B → m ≤ n * B →
      let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared base : StructuredCalls.State 40 896,
      (∀ i, (a.stacks i).length ≤ startupBound) → LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startupBound + NativeLeafSetup.parameterTime m B startupBound
        (a.stacks 782).length (a.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤ retainedBound m B startupBound a prepared) →
      let L := NativeLeafRun.commonBound n m B (retainedBound m B startupBound a prepared)
      max (max (startupBound + 1) (continuationSpace m B startupBound a prepared))
        (NativeLeafRun.roundsSpace base n m (SparseCode.distanceDenom m B) L K) ≤
          max K (C * (n + m + B + W + 16) ^ degree) := by
  obtain ⟨C, d, hprep⟩ := prepared_common_bound_polynomial
  let D := 1000000 * (C + 20001) ^ 3
  refine ⟨C + D, (d + 4) * 3, ?_⟩
  intro n m B W K hn hm hB hmb startupBound a prepared base ha hmeta hp hmword hbase L
  let X := n + m + B + W + 16
  let R := retainedBound m B startupBound a prepared
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hh := hprep n m B W hn hm hB hmb a prepared ha hmeta hp
  have hL : L ≤ C * X ^ d := (le_max_right _ _).trans hh
  have hS := HashQueryInputBounds.commonCap_bounds n m B R
  have hR : R ≤ L := by
    have hlin := Nat.le_self_pow (show 3 ≠ 0 by decide) (HashQueryInputBounds.commonCap n m B R)
    change R ≤ 16 * HashQueryInputBounds.commonCap n m B R ^ 3
    omega
  have hb : ∀ i, (base.stacks i).length ≤ L := fun i => (hbase i).trans hR
  have hround := common_rounds_space_le base n m B R K hmword hb
  have hdepth := (distanceDenom_polynomial m B).trans
    (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left (show B + m + 1 ≤ X by dsimp [X]; omega) 4))
  have hp4 : X ^ 4 ≤ X ^ (d + 4) := Nat.pow_le_pow_right hX (by omega)
  have hpd : X ^ d ≤ X ^ (d + 4) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : m + 1 ≤ X ^ (d + 4) := by
    apply (show m + 1 ≤ X by dsimp [X]; omega).trans
    exact Nat.le_self_pow (by omega) X
  have hz : m + SparseCode.distanceDenom m B + L + 1 ≤ (C + 20001) * X ^ (d + 4) := by
    have hl := hL.trans (Nat.mul_le_mul_left C hpd)
    have hd := hdepth.trans (Nat.mul_le_mul_left 20000 hp4)
    nlinarith only [hl, hd, hlinear]
  have hnumeric := Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hz 3)
  have heq : 1000000 * ((C + 20001) * X ^ (d + 4)) ^ 3 = D * X ^ ((d + 4) * 3) := by
    dsimp [D]
    rw [mul_pow, ← pow_mul, Nat.mul_assoc]
  rw [heq] at hnumeric
  have htarget := hnumeric.trans (Nat.mul_le_mul_right _ (show D ≤ C + D by omega))
  apply max_le
  · apply le_trans _ (le_max_right _ _)
    have ht := (le_max_left _ _).trans hh
    exact ht.trans ((Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (by omega))).trans
      (Nat.mul_le_mul_right _ (by omega)))
  · exact hround.trans (max_le_max le_rfl htarget)


/-- The actual disjoint choice and loaded input-word cap fix one polynomial
preparation and full selector space bound in original input length before all leaf calls. -/
theorem chosen_prepared_selector_space (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W K : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared base : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤ retainedBound m B L a prepared) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.roundsSpace base n m (SparseCode.distanceDenom m B)
          (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) K) ≤
          max K (C * (inputLength + 1) ^ degree) := by
  obtain ⟨C, degree, hprep⟩ := prepared_selector_space_polynomial
  obtain ⟨A, exponent, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  refine ⟨C * A ^ degree, exponent * degree, ?_⟩
  intro n inputLength m W K hn hm hinput hs B hmb hW L a prepared base ha hmeta hp hmword hbase
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  have h := hprep n m B W K hn hm hB hmb a prepared base ha hmeta hp hmword hbase
  have hcap := hsize n inputLength m W hinput hs hmb hW
  apply h.trans
  apply max_le_max le_rfl
  have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hcap degree)
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hh

open SqrtLog.CodeSetupCost

/-- The time bound of the actual full preparation is a fixed polynomial in
its ordinary input parameters and the original explicit worst-case code
budget. Startup, parameter arithmetic, depth expansion and suffix work are
included in the same expression. -/
theorem full_time_polynomial_envelope :
    ∃ C degree : ℕ, ∀ n m B W H wordCap : ℕ, 0 < m → 0 < B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      SparseCode.localRows m B ≤ H → SparseCode.degree m B ≤ H →
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H →
      SparseCode.dimension m B ≤ H →
      (prepared.stacks 800).length ≤ wordCap →
      (prepared.stacks 801).length ≤ wordCap →
      NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared ≤
        C * (n + m + B + W + envelope 3000000000000 H wordCap + 16) ^ degree := by
  obtain ⟨Cp, dp, hparameter⟩ := NativeLeafSetup.canonicalParameterTime_polynomial
  refine ⟨30000000000000000001 * (Cp + 20001) ^ 6, (dp + 4) * 6, ?_⟩
  intro n m B W H wordCap hm hB L a prepared ha hmeta hp ht hD hd hr hq hDl
  let A := L + NativeLeafSetup.parameterTime m B L
    (a.stacks 782).length (a.stacks 786).length
  let X := n + m + B + W + envelope 3000000000000 H wordCap + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA : A + 1 ≤ Cp * X ^ dp :=
    (hparameter n m B W _ _ hm hB (ha 782) (ha 786)).trans
      (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left (by dsimp [X]; omega) dp))
  have hpowers : X ^ dp ≤ X ^ (dp + 4) := Nat.pow_le_pow_right hX (by omega)
  have hfour : X ^ 4 ≤ X ^ (dp + 4) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : X ≤ X ^ (dp + 4) := Nat.le_self_pow (by omega) X
  have hdepth : SparseCode.distanceDenom m B ≤ 20000 * X ^ 4 :=
    (distanceDenom_polynomial m B).trans (Nat.mul_le_mul_left 20000
      (Nat.pow_le_pow_left (by dsimp [X]; omega) 4))
  have hE : envelope 3000000000000 H wordCap ≤ X := by dsimp [X]; omega
  have hZ : A + SparseCode.distanceDenom m B + envelope 3000000000000 H wordCap + 1 ≤
      (Cp + 20001) * X ^ (dp + 4) := by
    have hAp := hA.trans (Nat.mul_le_mul_left Cp hpowers)
    have hdep := hdepth.trans (Nat.mul_le_mul_left 20000 hfour)
    nlinarith only [hAp, hdep, hE, hlinear]
  have ht0 := continuationTime_le_envelope m B L H wordCap a prepared
    ha hmeta hp ht hD hd hr hq hDl
  have ht1 := ht0.trans (Nat.mul_le_mul_left 30000000000000000000
    (Nat.pow_le_pow_left hZ 6))
  have heq : ((Cp + 20001) * X ^ (dp + 4)) ^ 6 =
      (Cp + 20001) ^ 6 * X ^ ((dp + 4) * 6) := by rw [mul_pow, ← pow_mul]
  rw [heq] at ht1
  have hsA : NativeLeafSetup.canonicalStartTime n m W ≤ A := by dsimp [A, L]; omega
  have hcoef : Cp ≤ (Cp + 20001) ^ 6 :=
    (show Cp ≤ Cp + 20001 by omega).trans (Nat.le_self_pow (by decide) _)
  have hexp : X ^ dp ≤ X ^ ((dp + 4) * 6) := Nat.pow_le_pow_right hX (by omega)
  have hstart : NativeLeafSetup.canonicalStartTime n m W ≤
      (Cp + 20001) ^ 6 * X ^ ((dp + 4) * 6) :=
    hsA.trans ((Nat.le_of_succ_le hA).trans (Nat.mul_le_mul hcoef hexp))
  change _ ≤ 30000000000000000001 * (Cp + 20001) ^ 6 * X ^ ((dp + 4) * 6)
  nlinarith only [ht1, hstart]

/-- The actual chosen sparsification bound and an independently produced
input-word cap replace all ordinary preparation parameters by the original
input length. The old explicit code envelope remains visible. -/
theorem chosen_preparation_time_envelope (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W H wordCap : ℕ,
      0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      SparseCode.localRows m B ≤ H → SparseCode.degree m B ≤ H →
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H →
      SparseCode.dimension m B ≤ H →
      (prepared.stacks 800).length ≤ wordCap →
      (prepared.stacks 801).length ≤ wordCap →
      NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared ≤
        C * (inputLength + envelope 3000000000000 H wordCap + 1) ^ degree := by
  obtain ⟨Cp, dp, hprep⟩ := full_time_polynomial_envelope
  obtain ⟨Cs, ds, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  refine ⟨Cp * (Cs + 1) ^ dp, (ds + 1) * dp, ?_⟩
  intro n inputLength m W H wordCap hm hn hs B hmb hW L a prepared ha hmeta hp ht hD hd hr hq hDl
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  let X := inputLength + envelope 3000000000000 H wordCap + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hcap := hsize n inputLength m W hn hs hmb hW
  change n + m + B + W + 16 ≤ Cs * (inputLength + 1) ^ ds at hcap
  have hb : inputLength + 1 ≤ X := by dsimp [X]; omega
  have hpoly : (inputLength + 1) ^ ds ≤ X ^ (ds + 1) :=
    (Nat.pow_le_pow_left hb ds).trans (Nat.pow_le_pow_right hX (by omega))
  have hlinear : X ≤ X ^ (ds + 1) := Nat.le_self_pow (by omega) X
  have hcode : envelope 3000000000000 H wordCap ≤ X := by dsimp [X]; omega
  have htotal : n + m + B + W + envelope 3000000000000 H wordCap + 16 ≤
      (Cs + 1) * X ^ (ds + 1) := by
    have hh := hcap.trans (Nat.mul_le_mul_left Cs hpoly)
    nlinarith only [hh, hlinear, hcode]
  have hp0 := hprep n m B W H wordCap hm hB a prepared ha hmeta hp ht hD hd hr hq hDl
  have hp1 := hp0.trans (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left htotal dp))
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hp1

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

private theorem preparation_envelope_runtimeBound
    (K e C p inputLength n A E newCost : ℕ)
    (hA : A + 1 ≤ K * (inputLength + 1) ^ e)
    (hE : (E : ℝ) ≤ ((A : ℝ) + 1) ^ 6 * (2 : ℝ) ^ runtimeScale n)
    (hnew : newCost ≤ C * (inputLength + E + 1) ^ p) :
    (newCost : ℝ) ≤ runtimeBound
      (((C : ℝ) + 1) * (2 * ((K : ℝ) + 1) ^ 6) ^ p)
      p ((e * 6 + 1) * p) inputLength n := by
  have hK : (1 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 K
  have hbase : (1 : ℝ) ≤ (inputLength : ℝ) + 1 := by
    exact_mod_cast Nat.le_add_left 1 inputLength
  have hword : ((A : ℝ)+1)^6 ≤ ((K : ℝ)+1)^6 *
      ((inputLength : ℝ)+1)^(e*6+1) := by
    have hAR : (A : ℝ)+1 ≤ (K : ℝ)*((inputLength : ℝ)+1)^e := by exact_mod_cast hA
    have hpow := pow_le_pow_left₀ (by positivity) hAR 6
    rw [mul_pow, ←pow_mul] at hpow
    exact hpow.trans (mul_le_mul
      (pow_le_pow_left₀ (by positivity) (by linarith) 6)
      (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity))
  have hEbound : (E : ℝ) ≤ runtimeBound (((K : ℝ)+1)^6) 1 (e*6+1) inputLength n := by
    apply hE.trans
    simpa only [runtimeBound,one_mul] using
      mul_le_mul_of_nonneg_right hword (Real.rpow_nonneg (by norm_num) _)
  have hnewR : (newCost : ℝ) ≤ ((C : ℝ)+1)*((E : ℝ)+inputLength+1)^p := by
    have hR : (newCost : ℝ) ≤ (C : ℝ)*((inputLength : ℝ)+E+1)^p := by
      exact_mod_cast hnew
    apply hR.trans
    rw [show (inputLength : ℝ)+E+1=(E : ℝ)+inputLength+1 by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hfinal := fixedPolynomialCost_bound (one_le_pow₀ hK (n := 6))
    (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (C : ℝ)+1)
    (show 1 ≤ e*6+1 by omega) inputLength n p E newCost hEbound hnewR
  simpa only [mul_one] using hfinal

/-- All actual preparation costs satisfy the unchanged runtime scale above a
fixed cutoff. Both the dimension envelope and its physical word factor are
derived from the chosen occurrence bound and actual metadata producer caps. -/
theorem chosen_preparation_runtimeBound (k wordCoefficient wordDegree : ℕ) :
    ∃ C : ℝ, ∃ exponent degree cutoff : ℕ, 1 ≤ C ∧
      ∀ n inputLength m W : ℕ, cutoff ≤ n → 0 < m → n ≤ inputLength →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      ((NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared : ℕ) : ℝ) ≤
        runtimeBound C exponent degree inputLength n := by
  obtain ⟨Ct, dt, htime⟩ := chosen_preparation_time_envelope k wordCoefficient wordDegree
  obtain ⟨Cs, ds, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  obtain ⟨Cm, dm, hmetaSize⟩ := NativeLeafSetup.canonicalParameterTime_polynomial
  let qi := 2*(k-1)+1
  let heightCoefficient := 320000*(qi+2)^3+qi+4
  obtain ⟨cutoff,hcutoff⟩ := Filter.eventually_atTop.mp
    (((chosen_sparseBound_eventually_le_log2_power k).and
      (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1))).and
      (eventually_envelope_with_words 3000000000000 heightCoefficient (2*qi+3)))
  let K := Cm * Cs ^ dm
  let codeDegree := ds*dm*6+1
  let codeCoefficient : ℝ := ((K : ℝ)+1)^6
  refine ⟨((Ct : ℝ)+1)*(2*codeCoefficient)^dt,dt,codeDegree*dt,cutoff,?_,?_⟩
  · have hK : 1 ≤ codeCoefficient := by dsimp [codeCoefficient]; exact one_le_pow₀ (by exact_mod_cast Nat.le_add_left 1 K)
    have hpow : 1 ≤ (2*codeCoefficient)^dt := one_le_pow₀ (by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) Ct]
  intro n inputLength m W hn hm hinput B hmb hW L a prepared ha hmeta hp
  obtain ⟨⟨hBn,hs⟩,hcode⟩ := hcutoff n hn
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  have hBpoly : B ≤ Asymptotic.L n ^ qi := by simpa only [B,qi,Asymptotic.L] using hBn
  let H := heightCoefficient * Asymptotic.L n ^ (2*qi+3)
  let A := L + NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  have hordinary := hsize n inputLength m W hinput hs hmb hW
  have hmetaOrd := hmetaSize n m B W _ _ hm hB (ha 782) (ha 786)
  have hX : n+m+W+16 ≤ Cs*(inputLength+1)^ds := by
    change n+m+B+W+16 ≤ _ at hordinary
    omega
  have hA : A+1 ≤ K*(inputLength+1)^(ds*dm) := by
    apply hmetaOrd.trans
    have h := Nat.mul_le_mul_left Cm (Nat.pow_le_pow_left hX dm)
    simpa only [K,mul_pow,←pow_mul,Nat.mul_assoc] using h
  obtain ⟨ht,hD,hd,hr⟩ := produced_dimensions_le n m B qi hm hB hmb hBpoly
  have htimeNat := htime n inputLength m W H A hm hinput hs hmb hW a prepared
    ha hmeta hp ht hD hd hr (hp 800) (hp 801)
  let E := envelope 3000000000000 H A
  have hE := hcode H A le_rfl
  exact preparation_envelope_runtimeBound K (ds*dm) Ct dt inputLength n A E
    (NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared)
    hA hE htimeNat
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
