import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchPrepared
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeFiberBudgetBounds

namespace OAI.Algorithms

/-! Bounds for the actual serialized inputs and Side preparation of the
local-basis batch. Every length below comes from the concrete encoding. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchBounds

open LocalBasisBatchProgram

variable {r Q Δ : ℕ}

theorem sideBytes_length_le (t g U : ℕ)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    (TypeEnumeration.sideBytes r Q Δ t g).length ≤ U :=
  (List.length_filter_le _ _).trans hu

theorem sideList_length_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (U : ℕ) (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length ≤ U := by
  have h := sideBytes_length_le t.val g.val U hu
  rwa [← TypeEnumeration.sideList_bytes hr hQ t g, List.length_map] at h

theorem encodedUniversal_le (hr : 0 < r) (hQ : 0 < Q) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    (ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)).length ≤
      5 * (U + 1)^4 := by
  let X := U + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h14 : X ≤ X^4 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 4 by decide)
  have ht := MatrixEntryBudgetBounds.typeWidth_le hrU hQU hΔU
  change CollisionProgram.typeWidth r Q Δ ≤ X^3 at ht
  rw [ConstraintMatrixSizeBasics.encodeRecords_length_of_uniform _ _
    (TypeEnumeration.universalBytes_width hr hQ)]
  change _ ≤ 5 * X^4
  calc
    _ ≤ X * (2 * X^3 + 2) + 1 := by gcongr ; dsimp [X] at * ; omega
    _ ≤ _ := by nlinarith only [hX, h14]

theorem encodedSide_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (U : ℕ) (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t.val g.val)).length ≤
      5 * (U + 1)^4 := by
  let X := U + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h14 : X ≤ X^4 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 4 by decide)
  have ht := MatrixEntryBudgetBounds.typeWidth_le hrU hQU hΔU
  change CollisionProgram.typeWidth r Q Δ ≤ X^3 at ht
  have hn := sideList_length_le hr hQ t g U hu
  rw [ConstraintMatrixSizeBasics.encodedSide_length hr hQ t g]
  change _ ≤ 5 * X^4
  calc
    _ ≤ X * (2 * X^3 + 2) + 1 := by gcongr ; dsimp [X] at * ; omega
    _ ≤ _ := by nlinarith only [hX, h14]

theorem encodedAlphabet_length (p : ℕ) [Fact p.Prime] (alphabet : List (ZMod p)) :
    (ProgramEncoding.encodeRecords
      (alphabet.map (BlockSearchPredicate.scalarCode p).block)).length =
        alphabet.length * (4 * MatrixWordEncoding.width p + 4) + 1 := by
  rw [ConstraintMatrixSizeBasics.encodeRecords_length_of_uniform _
    (2 * MatrixWordEncoding.width p + 1) (by
      intro bits hb
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
      exact (BlockSearchPredicate.scalarCode p).length_block x)]
  rw [List.length_map]
  ring

theorem contextExtent_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hcard : alphabet.length = p) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    contextExtent (canonicalContext p r Q Δ coefficients alphabet) ≤ 20 * (U + 1)^4 := by
  let X := U + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h14 : X ≤ X^4 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 4 by decide)
  have h24 : X^2 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have htypes := encodedUniversal_le hr hQ U hrU hQU hΔU hu
  change _ ≤ 5 * X^4 at htypes
  have hc : coefficients.length * (2 * MatrixWordEncoding.width p + 1) ≤ 3 * X^2 := by
    calc
      _ ≤ X * (2 * X + X) := by gcongr <;> dsimp [X] at * <;> omega
      _ = _ := by ring
  have ha : p * (4 * MatrixWordEncoding.width p + 4) + 1 ≤ 5 * X^2 := by
    have hsmall : 4 * MatrixWordEncoding.width p + 4 ≤ 4 * X := by dsimp [X]; omega
    calc
      _ ≤ X * (4 * X) + 1 := by gcongr ; dsimp [X] at * ; omega
      _ ≤ _ := by nlinarith only [hX]
  have hrest : (MatrixWordEncoding.width p + 1) + MatrixWordEncoding.width p +
      coefficients.length + r + Q + Δ ≤ 6 * X := by dsimp [X]; omega
  simp only [contextExtent, canonicalContext, MatrixWordEncoding.modulus_length,
    MatrixWordEncoding.zero_length, CoefficientPascalProgram.valueWords_length,
    TypeIndexProgram.unary, List.length_replicate, encodedAlphabet_length, hcard]
  change _ ≤ 20 * X^4
  omega

theorem colorExtent_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hcard : alphabet.length = p)
    (t : Fin Q) (g : Fin r) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    colorExtent p r Q Δ coefficients alphabet t.val g.val ≤ 40 * (U + 1)^4 := by
  let X := U + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h14 : X ≤ X^4 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 4 by decide)
  have h24 : X^2 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have hc := contextExtent_le p hr hQ coefficients alphabet hcard U hrU hQU hΔU hR hp hw hu
  have he := encodedSide_le hr hQ t g U hrU hQU hΔU hu
  have hn := sideBytes_length_le t.val g.val U hu
  have hqr : Q * r ≤ X^2 := by
    calc
      _ ≤ X * X := by gcongr <;> dsimp [X] <;> omega
      _ = _ := by ring
  have hnn : (TypeEnumeration.sideBytes r Q Δ t.val g.val).length *
      (TypeEnumeration.sideBytes r Q Δ t.val g.val).length ≤ X^2 := by
    calc
      _ ≤ X * X := by gcongr <;> dsimp [X] <;> omega
      _ = _ := by ring
  have hrest : Q + r + (TypeEnumeration.sideBytes r Q Δ t.val g.val).length + 1 ≤ 4 * X := by
    dsimp [X]; omega
  change _ ≤ 20 * X^4 at hc
  change _ ≤ 5 * X^4 at he
  change _ ≤ 40 * X^4
  unfold colorExtent
  omega

theorem sideFilter_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (U : ℕ) (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    TypeFiberProgram.budget false ⟨r, t.val, g.val, Q * r, 0⟩
      (TypeEnumeration.universalBytes r Q Δ) ≤ 400 * (U + 1)^4 := by
  let X := U + 1
  let index := TypeEnumeration.headIndex r t.val g.val
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h14 : X ≤ X^4 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 4 by decide)
  have h24 : X^2 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have h34 : X^3 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have ht : t.val ≤ X := by have := t.isLt; dsimp [X]; omega
  have hg : g.val ≤ X := by have := g.isLt; dsimp [X]; omega
  have hindex : index ≤ 2 * X^2 := by
    calc
      _ ≤ X * X + X := by dsimp [index, TypeEnumeration.headIndex]; gcongr ; dsimp [X] ; omega
      _ ≤ _ := by nlinarith only [hX]
  have hhead : TypeIndexProgram.headCost r t.val g.val ≤ 100 * X^2 := by
    calc
      _ ≤ 7 * X + 7 * X + X * (7 * X + 7) + 16 := by
        unfold TypeIndexProgram.headCost
        gcongr ; dsimp [X] ; omega
      _ ≤ _ := by nlinarith only [hX]
  have hwidth := MatrixEntryBudgetBounds.typeWidth_le hrU hQU hΔU
  change CollisionProgram.typeWidth r Q Δ ≤ X^3 at hwidth
  have hf := TypeFiberBudgetBounds.bit_filter_budget_le true
    (TypeEnumeration.universalBytes r Q Δ) index (CollisionProgram.typeWidth r Q Δ)
    (TypeEnumeration.universalBytes_width hr hQ)
  have hfilter : TypeBitFilter.budget true (TypeEnumeration.universalBytes r Q Δ) index ≤
      200 * X^4 := by
    apply hf.trans
    calc
      _ ≤ X * (60 * X^3 + 12 * (2 * X^2) + 81) + 30 := by
        gcongr ; dsimp [X] at * ; omega
      _ ≤ _ := by nlinarith only [hX, h14, h34]
  change TypeIndexProgram.headCost r t.val g.val +
    TypeBitFilter.budget true (TypeEnumeration.universalBytes r Q Δ) index + 2 * index + 4 ≤ 400 * X^4
  nlinarith only [hhead, hfilter, hindex, hX, h14, h24]

theorem sideDimensionsCost_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (U : ℕ) (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    sideDimensionsCost r Q Δ t.val g.val ≤ 2000 * (U + 1)^8 := by
  let X := U + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h48 : X^4 ≤ X^8 := Nat.pow_le_pow_right hX (by decide)
  have h04 : 1 ≤ X^4 := Nat.one_le_pow _ _ hX
  have hf := sideFilter_le hr hQ t g U hrU hQU hΔU hu
  have he := encodedSide_le hr hQ t g U hrU hQU hΔU hu
  change _ ≤ 400 * X^4 at hf
  change _ ≤ 5 * X^4 at he
  have hd : ConstraintMatrixDimensions.budget (TypeEnumeration.sideBytes r Q Δ t.val g.val) ≤
      1152 * X^8 := by
    calc
      _ ≤ 32 * ((ProgramEncoding.encodeRecords
          (TypeEnumeration.sideBytes r Q Δ t.val g.val)).length + 1)^2 :=
        ConstraintMatrixDimensions.budget_le_length _
      _ ≤ 32 * (6 * X^4)^2 := by gcongr; omega
      _ = _ := by ring
  change _ ≤ 2000 * X^8
  unfold sideDimensionsCost
  omega

end SubexponentialSAT.Subexp.LocalBasisBatchBounds

end OAI.Algorithms
