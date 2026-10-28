import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProjection
import OAI.Algorithms.SubexponentialSAT.SubexpDenseParameters

namespace OAI.Algorithms

/-! Polynomial bounds for the concrete projection and addition scans.
Raw input sizes remain explicit; only output/query slots must be retained. -/

namespace SubexponentialSAT.SubexpDenseProjectionBounds

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpDenseSerialization
open SubexpDenseProgram

def recordBits (B I : ℕ) : ℕ := 4 * I + 16 * B + 6

def loadEnvelope (B I N L : ℕ) : ℕ :=
  4 + N * (6 * I + Projection.scanFactor B I * (L + 1) + 7) +
    11 * L + 7 * (1 + (2 * I + 2) * N) +
    8 * (1 + recordBits B I * N) + 46

def addEnvelope (B I N leftBits rightBits : ℕ) : ℕ :=
  loadEnvelope B I N (leftBits + rightBits + 1)

theorem recordBits_le (B I : ℕ) : recordBits B I ≤ 20 * (B + I + 1) := by
  unfold recordBits
  omega

theorem scanFactor_le (B I : ℕ) :
    Projection.scanFactor B I ≤ 30000 * (B + I + 1)^2 := by
  let X := B + I + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hB : B + 1 ≤ X := by dsimp [X]; omega
  have hI : I ≤ X := by dsimp [X]; omega
  have hBX : B ≤ X := by omega
  have hsq : (B + 1)^2 ≤ X^2 := Nat.pow_le_pow_left hB 2
  have hlin : X ≤ X^2 := by nlinarith
  have hpos : 1 ≤ X^2 := by nlinarith
  change Projection.scanFactor B I ≤ 30000 * X^2
  unfold Projection.scanFactor SubexpFlatAdd.wordCost
  nlinarith

theorem loadEnvelope_le (B I N L : ℕ) :
    loadEnvelope B I N L ≤ 40000 * (B + I + 1)^2 * (N + 1) * (L + 1) := by
  let X := B + I + 1
  let V := (N + 1) * (L + 1)
  let U := X^2 * V
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hI : I ≤ X := by dsimp [X]; omega
  have hI1 : I + 1 ≤ X := by dsimp [X]; omega
  have hX2 : 1 ≤ X^2 := by nlinarith
  have hXX : X ≤ X^2 := by nlinarith
  have hV : 1 ≤ V := by dsimp [V]; nlinarith
  have hNV : N ≤ V := by dsimp [V]; nlinarith
  have hLV : L ≤ V := by dsimp [V]; nlinarith
  have hVU : V ≤ U := by
    simpa only [U,one_mul] using Nat.mul_le_mul_right V hX2
  have hU : 1 ≤ U := hV.trans hVU
  have hN : N ≤ U := hNV.trans hVU
  have hL : L ≤ U := hLV.trans hVU
  have hXN : X * N ≤ U := Nat.mul_le_mul hXX hNV
  have hIN : I * N ≤ U := (Nat.mul_le_mul_right N hI).trans hXN
  have hI1N : (I + 1) * N ≤ U := (Nat.mul_le_mul_right N hI1).trans hXN
  have hrecord : recordBits B I * N ≤ 20 * U := by
    have h := Nat.mul_le_mul_right N (recordBits_le B I)
    change recordBits B I * N ≤ 20 * X * N at h
    nlinarith
  have hterm : X^2 * N * (L + 1) ≤ U := by
    calc
      _ ≤ X^2 * (N + 1) * (L + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ N))
      _ = U := by dsimp [U,V]; ring
  have hscan : N * (Projection.scanFactor B I * (L + 1)) ≤ 30000 * U := by
    calc
      _ ≤ N * ((30000 * X^2) * (L + 1)) := by
        gcongr
        exact scanFactor_le B I
      _ = 30000 * (X^2 * N * (L + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hterm
  have hbound : loadEnvelope B I N L ≤ 40000 * U := by
    unfold loadEnvelope
    nlinarith
  simpa only [U,V,X,Nat.mul_assoc] using hbound

theorem addEnvelope_le (B I N leftBits rightBits : ℕ)
    (hl : leftBits ≤ 1 + recordBits B I * N)
    (hr : rightBits ≤ 1 + recordBits B I * N) :
    addEnvelope B I N leftBits rightBits ≤
      2000000 * (B + I + 1)^3 * (N + 1)^3 := by
  let X := B + I + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hN : 1 ≤ N + 1 := by omega
  have hunit : 1 ≤ X * (N + 1) := by simpa using Nat.mul_le_mul hX hN
  have hrecord := Nat.mul_le_mul_right N (recordBits_le B I)
  change recordBits B I * N ≤ 20 * X * N at hrecord
  have hXN : X * N ≤ X * (N + 1) := Nat.mul_le_mul_left X (by omega)
  have hbits : leftBits + rightBits + 1 + 1 ≤ 44 * X * (N + 1) := by
    nlinarith
  have hpow : (N + 1)^2 ≤ (N + 1)^3 := Nat.pow_le_pow_right hN (by decide)
  calc
    _ ≤ 40000 * X^2 * (N + 1) * (leftBits + rightBits + 1 + 1) :=
      loadEnvelope_le B I N (leftBits + rightBits + 1)
    _ ≤ 40000 * X^2 * (N + 1) * (44 * X * (N + 1)) :=
      Nat.mul_le_mul_left _ hbits
    _ = 1760000 * X^3 * (N + 1)^2 := by ring
    _ ≤ 2000000 * X^3 * (N + 1)^3 := by
      gcongr
      all_goals omega

theorem query_length (D : ℕ) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a) :
    ∀ q ∈ (slots.map fixedKey).reverse, q.length ≤ indexBits D := by
  intro q hq
  have hm : q ∈ slots.map fixedKey := by simpa only [List.mem_reverse] using hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
  exact (fixedKey_length a (hs a ha)).le

theorem queryBytes_length (D : ℕ) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a) :
    (Projection.queryBytes slots).length ≤ 1 + (2 * indexBits D + 2) * slots.length := by
  simpa only [Projection.queryBytes,List.length_reverse,List.length_map] using
    Encoding.length_encodeList_upper id (slots.map fixedKey).reverse (indexBits D)
      (query_length D slots hs)

theorem retained_serialized_length (p D : ℕ) (P : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) :
    (encodeFixedQuarticCoefficients p D P).length =
      1 + recordBits (baseWidth p (D + 1)) (indexBits D) * P.length := by
  have h := encodeFixedCoefficients_length (quarticCodeBlockCode p D).block P
    (4 * baseWidth p (D + 1)) hP (fun a _ => by
      rw [← Projection.flat_encode_eq_block,SubexpFlatAdd.encode_length])
  calc
    _ = 1 + (4 * indexBits D + 4 * (4 * baseWidth p (D + 1)) + 6) * P.length := h
    _ = _ := by unfold recordBits; ring

theorem project_serialized_length (p D : ℕ) (ops : RingProgram (QuarticCode p D))
    (slots : List (RawIndex D)) (hs : ∀ a ∈ slots, Retained D a)
    (P : CoeffList D (QuarticCode p D)) :
    (encodeFixedQuarticCoefficients p D (programProject ops slots P).1).length =
      1 + recordBits (baseWidth p (D + 1)) (indexBits D) * slots.length := by
  have hp : ∀ a ∈ (programProject ops slots P).1, Retained D a.1 := by
    intro a ha
    have hm := List.mem_map_of_mem (f := Prod.fst) ha
    rw [programProject_keys] at hm
    exact hs a.1 hm
  rw [retained_serialized_length p D _ hp,SubexpExecution.project_length]

theorem add_serialized_length (p D : ℕ) (ops : RingProgram (QuarticCode p D))
    (slots : List (RawIndex D)) (hs : ∀ a ∈ slots, Retained D a)
    (P Q : CoeffList D (QuarticCode p D)) :
    (encodeFixedQuarticCoefficients p D (programAdd ops slots P Q).1).length =
      1 + recordBits (baseWidth p (D + 1)) (indexBits D) * slots.length := by
  exact project_serialized_length p D ops slots hs (appendWithCost P Q).1

theorem projectionTime_le (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (P : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a) :
    Projection.projectionTime p D M P slots ≤
      4 + slots.length * (6 * indexBits D +
        Projection.scanFactor (baseWidth p (D + 1)) (indexBits D) *
          ((encodeFixedQuarticCoefficients p D P).length + 1) + 7) := by
  have hcost : ∀ q ∈ (slots.map fixedKey).reverse,
      Projection.singleSlotCost p (D + 1) M q (Projection.encodedRaw P) ≤
        Projection.scanFactor (baseWidth p (D + 1)) (indexBits D) *
          ((encodeFixedQuarticCoefficients p D P).length + 1) := by
    intro q hq
    simpa only [Projection.encodedRaw_bytes] using
      Projection.singleSlotCost_le_serialized p (D + 1) M q (Projection.encodedRaw P)
        (indexBits D) (query_length D slots hs q hq)
  simpa only [Projection.projectionTime,List.length_reverse,List.length_map] using
    projectionController_cost (slots.map fixedKey).reverse
      (fun q => Projection.singleSlotCost p (D + 1) M q (Projection.encodedRaw P))
      (indexBits D) _ (query_length D slots hs) hcost

theorem additionTime_le (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a) :
    Projection.additionTime p D M P Q slots ≤
      4 + slots.length * (6 * indexBits D +
        Projection.scanFactor (baseWidth p (D + 1)) (indexBits D) *
          ((encodeFixedQuarticCoefficients p D P).length +
            (encodeFixedQuarticCoefficients p D Q).length + 2) + 7) := by
  have hcost : ∀ q ∈ (slots.map fixedKey).reverse,
      Projection.additionSlotCost p (D + 1) M q (Projection.encodedRaw P) (Projection.encodedRaw Q) ≤
        Projection.scanFactor (baseWidth p (D + 1)) (indexBits D) *
          ((encodeFixedQuarticCoefficients p D P).length +
            (encodeFixedQuarticCoefficients p D Q).length + 2) := by
    intro q hq
    simpa only [Projection.encodedRaw_bytes] using
      Projection.additionSlotCost_le_serialized p (D + 1) M q
        (Projection.encodedRaw P) (Projection.encodedRaw Q)
        (indexBits D) (query_length D slots hs q hq)
  simpa only [Projection.additionTime,List.length_reverse,List.length_map] using
    projectionController_cost (slots.map fixedKey).reverse
      (fun q => Projection.additionSlotCost p (D + 1) M q
        (Projection.encodedRaw P) (Projection.encodedRaw Q))
      (indexBits D) _ (query_length D slots hs) hcost

end SubexponentialSAT.SubexpDenseProjectionBounds

end OAI.Algorithms
