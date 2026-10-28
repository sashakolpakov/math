import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NormalizationSpace

open BitProgram
open SubexpNormalizationProgram (Data Ready program)
open SubexpNormalizationCorrectness (normalizedBody)

theorem canonical_body_trace_space {n : ℕ} (F : SAT.CNF (Fin n)) (d : Data)
    (hsource : d.stacks 13 = Encoding.encodeCNFBody F) (hready : Ready d) :
    ∃ (steps : ℕ) (e : Data),
      steps ≤ 3300 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
      Ready e ∧ e.stacks 13 = normalizedBody F ∧
      Trace program steps (d.withPC (some program.entry)) (e.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (d.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ Encoding.formulaBitLength F +
          3300 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
        ∀ i, (intermediate.stacks i).length ≤ Encoding.formulaBitLength F +
          3300 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  have hstacks : d.stacks = fun i =>
      if i = 13 then Encoding.encodeCNFBody F else [] := by
    funext i
    by_cases hi : i = 13
    · subst i
      simpa using hsource
    · simpa [hi] using hready i hi
  have hbits : dataBits (d.withPC (some program.entry)) =
      (Encoding.encodeCNFBody F).length := by
    change stackBits d.stacks = _
    rw [hstacks]
    have hlengths (i : Fin 16) :
        (if i = 13 then Encoding.encodeCNFBody F else []).length =
          if i = 13 then (Encoding.encodeCNFBody F).length else 0 := by
      split_ifs <;> rfl
    simp only [stackBits, hlengths]
    simp
  have hinput : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
    rw [Encoding.formulaBitLength_eq]
    omega
  obtain ⟨e, he, hout, steps, hs, ht⟩ :=
    SubexpNormalizationCorrectness.canonical_body_inputLength_runsIn F d hsource hready
  refine ⟨steps, e, hs, he, hout, ht, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits program htrace
  rw [hbits] at hgrowth
  have htotal : dataBits intermediate ≤ Encoding.formulaBitLength F +
      3300 * (Encoding.formulaBitLength F + 1) ^ 2 := by omega
  refine ⟨htotal, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
    (Finset.mem_univ i)).trans htotal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NormalizationSpace
