import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramReadbackReduce

namespace OAI.Algorithms

/-! Complete physical count readback for the supplied irreducible model.
The dimension and scalar width occur only in data and bounds. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Readback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount
open RingProgram SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpLiftRing SubexponentialSAT.BinaryArithmetic

theorem flat_firstWord {d B : ℕ} (hd : 0 < d) (x : RingProgram.Code (Word B) d) :
    ∃ suffix, flat x = (x ⟨0, hd⟩).val ++ suffix ∧ suffix.length = (d - 1) * B := by
  cases d with
  | zero => omega
  | succ d =>
      refine ⟨flat (fun i : Fin d => x i.succ), ?_, ?_⟩
      · simp [flat, List.ofFn_succ]
      · simp

theorem model_countProgram_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : RingProgram.Code (ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (modelRing t ht hd a M cache).decode x = (z : a.O t))
    (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t) (hwidth : width.length = baseWidth 3 t) :
    ∃ finalRegs word, BinaryArithmetic.toNat word = z ∧
      word.length = modulus.length + baseWidth 3 t ∧
      RunsIn countProgram (budget (baseWidth 3 t) modulus (flat x))
        ((start regs modulus width (flat x)).withPC (some countProgram.entry))
        (⟨none, finalRegs, store word modulus [] width⟩ : Cfg 8 8 _) := by
  have hB : 0 < baseWidth 3 t := by rw [ternary_baseWidth]; omega
  obtain ⟨suffix, hs, _⟩ := flat_firstWord hd x
  obtain ⟨finalRegs, hr⟩ := countProgram_run hB (x ⟨0, hd⟩).val suffix
    (x ⟨0, hd⟩).property regs modulus width hwidth
  refine ⟨finalRegs, ModularArithmetic.reduce modulus (x ⟨0, hd⟩).val,
    reduced_firstWord_value t ht hd a M cache x z hz hx modulus hm, ?_, ?_⟩
  · simp [ModularArithmetic.reduce_length, (x ⟨0, hd⟩).property]
  · simpa only [hs] using hr

end SubexponentialSAT.SqrtLog.LeafProgram.Readback

end OAI.Algorithms
