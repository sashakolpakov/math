import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchBoundary
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchInputs
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientPascalProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPredicate

namespace OAI.Algorithms

/-!
# Canonical inputs at a local-basis color boundary

The actual Side-filter/count execution is specialized to the loop boundary
with canonical scalar and type encodings. The physical word bound excludes
only the two caller-owned fuels and two accumulated-output words.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls
open TypeIndexProgram (unary)

def canonicalContext (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p)) : Context where
  types := ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)
  modulus := MatrixWordEncoding.modulus p
  zero := MatrixWordEncoding.zero p
  coefficients := CoefficientPascalProgram.valueWords p coefficients
  length := unary coefficients.length
  colors := unary r
  positions := unary Q
  slots := unary Δ
  alphabet := ProgramEncoding.encodeRecords (alphabet.map (BlockSearchPredicate.scalarCode p).block)

def contextExtent (ctx : Context) : ℕ :=
  ctx.types.length + ctx.modulus.length + ctx.zero.length + ctx.coefficients.length +
    ctx.length.length + ctx.colors.length + ctx.positions.length + ctx.slots.length +
    ctx.alphabet.length

def colorExtent (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p)) (t g : ℕ) : ℕ :=
  contextExtent (canonicalContext p r Q Δ coefficients alphabet) + Q * r + Q + r +
    (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t g)).length +
    (TypeEnumeration.sideBytes r Q Δ t g).length +
    (TypeEnumeration.sideBytes r Q Δ t g).length * (TypeEnumeration.sideBytes r Q Δ t g).length + 1

theorem colorExtent_pos (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p)) (t g : ℕ) :
    0 < colorExtent p r Q Δ coefficients alphabet t g := by
  unfold colorExtent
  omega

theorem canonicalContext_lengths (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p)) :
    (canonicalContext p r Q Δ coefficients alphabet).colors.length = r ∧
    (canonicalContext p r Q Δ coefficients alphabet).positions.length = Q ∧
    (canonicalContext p r Q Δ coefficients alphabet).slots.length = Δ ∧
    (canonicalContext p r Q Δ coefficients alphabet).length.length = coefficients.length := by
  simp [canonicalContext, unary]

theorem inputState_length_le_contextExtent (ctx : Context) (regs : Fin 32 → Bool)
    (j : Fin 128) : ((inputState ctx regs).stacks j).length ≤ contextExtent ctx := by
  simp only [inputState]
  split_ifs <;> simp [contextExtent] <;> omega

theorem outputState_length_le_contextExtent (ctx : Context) (width : Word)
    (regs : Fin 32 → Bool) (j : Fin 128) :
    ((outputState ctx width [] regs).stacks j).length ≤ contextExtent ctx + width.length := by
  by_cases h127 : j = 127
  · subst j
    simp [outputState]
  · by_cases h114 : j = 114
    · subst j
      simp [outputState]
    · have h := inputState_length_le_contextExtent ctx regs j
      have h' : ((inputState ctx regs).stacks j).length ≤ contextExtent ctx + width.length := by omega
      simpa [outputState, h127, h114] using h'

theorem boundary_low_empty (ctx : Context) (width : Word) (t g : ℕ)
    (oa ia ofuel ifuel : Word) (regs : Fin 32 → Bool)
    (j : Fin 128) (hj : j.val < 107) :
    (boundaryState ctx width t g oa ia ofuel ifuel regs).stacks j = [] := by
  have hne (k : Fin 128) (hk : 107 ≤ k.val) : j ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    omega
  simp [boundaryState, outputState, inputState,
    hne 107 (by decide), hne 108 (by decide), hne 109 (by decide),
    hne 110 (by decide), hne 111 (by decide), hne 112 (by decide),
    hne 113 (by decide), hne 114 (by decide), hne 115 (by decide),
    hne 116 (by decide), hne 117 (by decide), hne 118 (by decide),
    hne 119 (by decide), hne 120 (by decide), hne 121 (by decide),
    hne 122 (by decide), hne 127 (by decide)]

/-- The bound excludes exactly the two fuels 119/120 and accumulators
121/122. Those words may contain arbitrary caller data. -/
theorem boundary_length_le (ctx : Context) (width : Word) (t g : ℕ)
    (oa ia ofuel ifuel : Word) (regs : Fin 32 → Bool)
    (j : Fin 128) (hj : j.val < 119 ∨ 123 ≤ j.val) :
    ((boundaryState ctx width t g oa ia ofuel ifuel regs).stacks j).length ≤
      contextExtent ctx + width.length + t + g := by
  have hne (k : Fin 128) (hk : 119 ≤ k.val ∧ k.val < 123) : j ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    rcases hj with hj | hj <;> omega
  have h119 := hne 119 (by decide)
  have h120 := hne 120 (by decide)
  have h121 := hne 121 (by decide)
  have h122 := hne 122 (by decide)
  by_cases h117 : j = 117
  · subst j
    simpa [boundaryState] using
      (show t ≤ contextExtent ctx + width.length + t + g by omega)
  · by_cases h118 : j = 118
    · subst j
      simp [boundaryState]
    · have h := outputState_length_le_contextExtent ctx width regs j
      calc
        _ = ((outputState ctx width [] regs).stacks j).length := by
          simp [boundaryState, h117, h118, h119, h120, h121, h122]
        _ ≤ contextExtent ctx + width.length := h
        _ ≤ contextExtent ctx + width.length + t + g := by omega

def preparedColorStacks (r Q Δ t g : ℕ) (a : Data) : Fin 128 → Word :=
  let side := TypeEnumeration.sideBytes r Q Δ t g
  Function.update (Function.update (Function.update a.stacks 53
    (ProgramEncoding.encodeRecords side)) 123 (unary side.length))
    124 (unary (side.length * side.length))

theorem preparedColorStacks_side (r Q Δ t g : ℕ) (a : Data) :
    preparedColorStacks r Q Δ t g a 53 =
      ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t g) := by
  simp [preparedColorStacks]

theorem preparedColorStacks_dimensions (r Q Δ t g : ℕ) (a : Data) :
    preparedColorStacks r Q Δ t g a 123 = unary (TypeEnumeration.sideBytes r Q Δ t g).length ∧
    preparedColorStacks r Q Δ t g a 124 =
      unary ((TypeEnumeration.sideBytes r Q Δ t g).length *
        (TypeEnumeration.sideBytes r Q Δ t g).length) := by
  simp [preparedColorStacks]

theorem preparedColorStacks_frame (r Q Δ t g : ℕ) (a : Data) (j : Fin 128)
    (h53 : j ≠ 53) (h123 : j ≠ 123) (h124 : j ≠ 124) :
    preparedColorStacks r Q Δ t g a j = a.stacks j := by
  simp [preparedColorStacks, h53, h123, h124]

theorem preparedColor_length_le (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p)) (t g : ℕ) (ht : t < Q) (hg : g < r)
    (oa ia ofuel ifuel : Word) (regs : Fin 32 → Bool)
    (j : Fin 128) (hj : j.val < 119 ∨ 123 ≤ j.val) :
    (preparedColorStacks r Q Δ t g
      (boundaryState (canonicalContext p r Q Δ coefficients alphabet) (unary (Q * r))
        t g oa ia ofuel ifuel regs) j).length ≤
      colorExtent p r Q Δ coefficients alphabet t g := by
  by_cases h124 : j = 124
  · subst j
    simp only [preparedColorStacks, Function.update_self, unary, List.length_replicate]
    unfold colorExtent
    omega
  · by_cases h123 : j = 123
    · subst j
      rw [(preparedColorStacks_dimensions r Q Δ t g _).1]
      simp only [unary, List.length_replicate]
      unfold colorExtent
      omega
    · by_cases h53 : j = 53
      · subst j
        rw [preparedColorStacks_side]
        unfold colorExtent
        omega
      · rw [preparedColorStacks_frame _ _ _ _ _ _ _ h53 h123 h124]
        have h := boundary_length_le (canonicalContext p r Q Δ coefficients alphabet)
          (unary (Q * r)) t g oa ia ofuel ifuel regs j hj
        have hwidth : (unary (Q * r)).length = Q * r := by simp [unary]
        rw [hwidth] at h
        unfold colorExtent
        omega

/-- Actual preparation at a live loop boundary. No execution, Side bytes,
or dimension is supplied as an assumption. The four caller-owned loop
words and every register from 8 upward are preserved. -/
theorem prepareColor_eval (p r Q Δ : ℕ) [Fact p.Prime]
    (coefficients alphabet : List (ZMod p)) (t g : ℕ) (ht : t < Q) (hg : g < r)
    (oa ia ofuel ifuel : Word) (regs : Fin 32 → Bool) :
    let a := boundaryState (canonicalContext p r Q Δ coefficients alphabet) (unary (Q * r))
      t g oa ia ofuel ifuel regs
    ∃ steps b, steps ≤ sideDimensionsCost r Q Δ t g ∧
      Eval (.seq sideFilter dimensions) steps a b ∧
      b.stacks = preparedColorStacks r Q Δ t g a ∧
      (∀ j : Fin 128, j.val < 119 ∨ 123 ≤ j.val →
        (b.stacks j).length ≤ colorExtent p r Q Δ coefficients alphabet t g) ∧
      ∀ j : Fin 32, 8 ≤ j.val → b.regs j = a.regs j := by
  let ctx := canonicalContext p r Q Δ coefficients alphabet
  let a := boundaryState ctx (unary (Q * r)) t g oa ia ofuel ifuel regs
  have low : ∀ j : Fin 128, j.val < 107 → a.stacks j = [] :=
    boundary_low_empty ctx (unary (Q * r)) t g oa ia ofuel ifuel regs
  obtain ⟨steps, b, hb, he, hs, hf⟩ := side_dimensions_eval r Q Δ t g a
    (by simp [a, ctx, boundaryState, outputState, inputState, canonicalContext])
    (by simp [a, ctx, boundaryState, outputState, inputState, canonicalContext])
    (by simp [a, boundaryState, unary])
    (by simp [a, boundaryState, unary])
    (by simp [a, boundaryState, outputState])
    (fun j hj => low j (by omega))
    (low 53 (by decide))
    (by simp [a, boundaryState, outputState, inputState])
    (by simp [a, boundaryState, outputState, inputState])
  refine ⟨steps, b, hb, he, hs, ?_, hf⟩
  intro j hj
  rw [hs]
  exact preparedColor_length_le p r Q Δ coefficients alphabet t g ht hg
    oa ia ofuel ifuel regs j hj

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
