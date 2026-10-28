import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCanonicalStore
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTExecution

namespace OAI.Algorithms

/-! The canonical represented state satisfies every physical input condition
of the actual per-node CRT correction program. -/

namespace SubexponentialSAT.SubexpCRTCanonicalInput

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexpLiftRing SubexpQuarticRing SubexpConvolutionControl
open SubexpPolynomialPowerProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
variable (t theta one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
  (width exponent : List Bool) (nodes : List (Coeff p D)) (index : List Bool) (J : Poly p D)

local notation "s" => canonical p D M t theta one minusOne width exponent nodes index J

omit [Fact p.Prime] in
theorem input (z : Coeff p D) (hw : width.length = baseWidth p (D + 1))
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false) :
    SubexpLocalCRTExecution.Input p D M s t z theta one minusOne width (fun _ => [])
      nodes index J := by
  have hinit (j : Fin 256) (hj : j.val < 205) :
      SubexpLocalInitializedScan.initial p D s j = s j := by
    apply SubexpLocalInitializedScan.initial_frame
    simp only [SubexpLocalInitializedScan.changed, List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · intro h; subst j; norm_num at hj
    constructor
    · intro h; subst j; norm_num at hj
    constructor
    · intro h; subst j; norm_num at hj
    constructor
    · intro h; subst j; norm_num at hj
    constructor <;> intro h <;> subst j <;> norm_num at hj
  have hn : ∀ i, (SubexpLocalInitializedScan.initial p D s)
      (SubexpLocalLinearFactorProgram.negatePorts i) =
        SubexpLocalSeedProgram.blankNegation minusOne.val M.bits width i := by
    intro i
    rw [SubexpLocalInitializedScan.initial_frame]
    · exact blank_negation p D M t theta one minusOne width exponent nodes index J i
    · fin_cases i <;> decide
  constructor
  · constructor
    · exact baseReady_congr p (D + 1) M s _ t width (fun _ => []) hinit
        (baseReady p D M t theta one minusOne width exponent nodes index J hw)
    · intro i
      rw [hinit _ (by
        dsimp [SubexpLocalLinearFactorProgram.addPorts]
        have := i.isLt
        omega)]
      fin_cases i <;> simp [canonical, store, context, SubexpLocalLinearFactorProgram.addPorts,
        SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks, Fin.addCases,
        Fin.coe_ofNat_eq_mod]
    · intro a
      exact SubexpLocalSeedProgram.negation_ready_update p (D + 1) M _ a minusOne width hn
    · intro i
      rw [hinit _ (bufferPorts_lt i)]
      fin_cases i <;> simp [canonical, store, bufferPorts,
        SubexpQuarticFlatMul.bankStore, Fin.coe_ofNat_eq_mod]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [SubexpLocalInitializedScan.initial, SubexpLocalCRTSetup.initialized,
          canonical, store, context]
    · simp [SubexpLocalInitializedScan.initial, SubexpLocalCRTSetup.initialized,
        canonical, store, context]
    · simp [SubexpLocalInitializedScan.initial, SubexpLocalCRTSetup.initialized,
        canonical, store, context]
    · simp [SubexpLocalInitializedScan.initial, SubexpLocalCRTSetup.initialized,
        canonical, store, context]
    · simp [SubexpLocalInitializedScan.initial, SubexpLocalCRTSetup.initialized,
        canonical, store, context]
    · exact hz
    · simp [SubexpLocalInitializedScan.initial, SubexpLocalCRTSetup.initialized,
        SubexpLocalCRTSetup.zeroArray_eq, encodeArray, hz]
  · intro i
    change s (SubexpConvolutionPair.highPort i) = _
    rw [canonical, store_high]
    simp only [context, SubexpQuarticPowerProgram.cleanNative, SubexpQuarticPowerCore.cleanNative]
  · exact blank_negation p D M t theta one minusOne width exponent nodes index J
  · intro i hi
    simp only [SubexpLocalCRTFrames.scratch, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp [canonical, store]
  · simp [canonical, store, context]
  · simp [canonical, store, context]
  · exact hz
  · simp [canonical, store, context]
  · simp [canonical, store, context]
  · simp [canonical, store, context]
  · simp [canonical, store, context]

end SubexponentialSAT.SubexpCRTCanonicalInput

end OAI.Algorithms
