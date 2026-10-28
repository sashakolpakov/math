import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativePackingBoundsAddress

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes LayoutProgram

theorem output_word_le {U : Type*} [DecidableEq U] (s : NativePacking.Spec U)
    (regs : Fin 16 → Bool) (i : Fin 48) :
    ((s.suffix.outputState regs).stacks i).length ≤ 34*sourceSize s^4 := by
  let S := sourceSize s
  have hS : 1 ≤ S := sourceSize_pos s
  have h4 : S ≤ S^4 := PackingBudgetArithmetic.le_power hS (by decide)
  have h24 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have hD : s.params.D ≤ S := dimension_le s
  have hW : s.params.width.length ≤ S := width_le s
  have hA : (ProgramEncoding.encodeRecords s.params.alphabet).length ≤ S := alphabet_bytes_le s
  have hR : s.params.rows.flatten.length ≤ S := by dsimp [S,sourceSize]; omega
  have hd : s.params.Δ ≤ S := by have := depth_le s; dsimp [S]; omega
  have h34 : S ≤ 34*S^4 := by nlinarith
  have hblocks : s.suffix.packing.blockCount ≤ 34*S^4 :=
    (block_count_le s).trans (hD.trans h34)
  have hleft : s.suffix.packing.leftovers.length ≤ 34*S^4 :=
    (leftovers_length_le s).trans (hD.trans h34)
  have hm : s.suffix.metadata.length ≤ 34*S^4 := metadata_output_bytes_le s
  have ha : s.suffix.addresses.length ≤ 34*S^4 := by
    calc
      _ ≤ addressBound s.params.D := addresses_length_le s
      _ ≤ addressBound S := by unfold addressBound; gcongr
      _ ≤ 34*S^4 := by unfold addressBound; nlinarith
  have hv : wordBound s.params.D ≤ 34*S^4 := by
    calc
      _ ≤ wordBound S := by unfold wordBound; gcongr
      _ ≤ 34*S^4 := by unfold wordBound; nlinarith
  have hs : s.suffix.storage.length ≤ 34*S^4 := (storage_length_le s).trans hv
  have hi : s.suffix.inverse.length ≤ 34*S^4 := (inverse_length_le s).trans hv
  by_cases h30 : i=30
  · subst i
    change (List.replicate s.suffix.packing.blockCount true).length ≤ 34*S^4
    simpa only [List.length_replicate] using hblocks
  by_cases h31 : i=31
  · subst i
    change (List.replicate s.suffix.packing.leftovers.length true).length ≤ 34*S^4
    simpa only [List.length_replicate] using hleft
  by_cases h32 : i=32
  · subst i
    exact hm
  by_cases h33 : i=33
  · subst i
    exact ha
  by_cases h34 : i=34
  · subst i
    exact hs
  by_cases h35 : i=35
  · subst i
    exact hi
  by_cases h40 : i=40
  · subst i
    change s.params.rows.flatten.length ≤ 34*S^4
    omega
  by_cases h41 : i=41
  · subst i
    change s.params.width.length ≤ 34*S^4
    omega
  by_cases h42 : i=42
  · subst i
    change (List.replicate s.params.D true).length ≤ 34*S^4
    simp only [List.length_replicate]
    omega
  by_cases h43 : i=43
  · subst i
    change (List.replicate s.params.Δ true).length ≤ 34*S^4
    simp only [List.length_replicate]
    omega
  by_cases h44 : i=44
  · subst i
    change 1 ≤ 34*S^4
    omega
  by_cases h45 : i=45
  · subst i
    change (ProgramEncoding.encodeRecords s.params.alphabet).length ≤ 34*S^4
    omega
  simp only [PackLabels.Spec.outputState,PackingProgram.outputState,PackingProgram.inputState,
    h30,h31,h32,h33,h34,h35,h40,h41,h42,h43,h44,h45,ite_false,List.length_nil]
  omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
