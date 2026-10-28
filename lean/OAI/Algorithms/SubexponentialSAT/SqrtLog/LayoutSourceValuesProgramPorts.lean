import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgramCached
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgramRelation

namespace OAI.Algorithms

/-! Fixed port maps and the persistent ring-cache frame for source-table
callbacks. These lemmas are independent of the integer numerator evaluator. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open IntegerRingLiftProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def numeratorRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def numeratorPorts (i : Fin 64) : Fin 256 :=
  if i = 50 then 253 else if i = 51 then 254 else Fin.castAdd 192 i

theorem numeratorRegs_injective : Function.Injective numeratorRegs :=
  Fin.castAdd_injective _ _

theorem numeratorPorts_injective : Function.Injective numeratorPorts := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  dsimp only [numeratorPorts] at hv
  split_ifs at hv <;> simp_all <;> omega

/-- Ring service invariants depend only on their own high registers. -/
theorem cachedReady_frame (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (base s : Store)
    (h : CachedReady t a M cache zero one minusOne base)
    (hf : ∀ i : Fin 256, 120 ≤ i.val → i ≠ 253 → i ≠ 254 → s i = base i) :
    CachedReady t a M cache zero one minusOne s := by
  have he (i : Fin 256) (hi : 120 ≤ i.val) (h253 : i ≠ 253) (h254 : i ≠ 254) :=
    hf i hi h253 h254
  have h120 := he 120 (by decide) (by decide) (by decide)
  have h194 := he 194 (by decide) (by decide) (by decide)
  have h201 := he 201 (by decide) (by decide) (by decide)
  have h202 := he 202 (by decide) (by decide) (by decide)
  have h203 := he 203 (by decide) (by decide) (by decide)
  have h204 := he 204 (by decide) (by decide) (by decide)
  have hn : HornerProgram.Services.NativeReady 3 t M cache (modelTable t a M cache) s := by
    refine ⟨⟨h120.trans h.native.workspace.1,?_⟩,h194.trans h.native.modulus,
      ?_,h203.trans h.native.zero,h201.trans h.native.table,?_⟩
    · intro i
      have hp := hf (ReconstructionProgram.RingAdapter.ports i)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      rw [hp]
      simpa only [ReconstructionProgram.RingAdapter.finalNative,h194,h201,h202,h203]
        using h.native.workspace.2 i
    · simpa only [h202] using h.native.width
    · simpa only [h204] using h.native.degree
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rcases h.clean with ⟨h1,h2,h3,h4,h5⟩
    exact ⟨h120.trans h1,(he 240 (by decide) (by decide) (by decide)).trans h2,
      (he 241 (by decide) (by decide) (by decide)).trans h3,
      (he 244 (by decide) (by decide) (by decide)).trans h4,
      (he 245 (by decide) (by decide) (by decide)).trans h5⟩
  · exact (he 249 (by decide) (by decide) (by decide)).trans h.zero
  · exact (he 250 (by decide) (by decide) (by decide)).trans h.one
  · exact (he 251 (by decide) (by decide) (by decide)).trans h.minusOne
  · exact (he 246 (by decide) (by decide) (by decide)).trans h.bits
  · exact (he 247 (by decide) (by decide) (by decide)).trans h.accumulator
  · exact (he 248 (by decide) (by decide) (by decide)).trans h.place
  · exact (he 255 (by decide) (by decide) (by decide)).trans h.output

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
