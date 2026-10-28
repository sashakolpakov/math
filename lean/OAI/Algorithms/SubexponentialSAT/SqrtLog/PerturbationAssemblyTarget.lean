import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyConstants

namespace OAI.Algorithms

/-! Dynamic target-jet cache installation. Full source-degree metadata at210
is untouched while the arithmetic count is temporarily changed to213. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram.Constructor

def initializeTarget : Code := .seq (saveReplace 213 193 237)
  (.seq (saveReplace 213 243 238) (.seq constructConstants
    (.seq (saveReplace 239 192 236) (clear 239))))

def targetScratch : List (Fin 256) :=
  [100,101,102,107,108,120,236,237,238,239,245,247,254]

def targetState (s : Store) (J W : ℕ) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update s
      193 (s 213)) 243 (s 213))
      192 (Counter.paddedBits W (s 207) (s 207) J))
      247 (Counter.paddedBits W (s 209) (s 208) J)) 254 (s 207))
      236 (s 192)) 237 (s 193)) 238 (s 243)

def targetBudget (s : Store) (J W : ℕ) : ℕ :=
  9*((s 192).length+(s 193).length+(s 243).length)+14*J+9*(J*W)+7*W+
    440*(J+1)*(W+1)+47

theorem initializeTarget_run (s : Store) (J W : ℕ)
    (hz : (s 207).length=W) (ho : (s 208).length=W) (hx : (s 209).length=W)
    (hJ : s 213=List.replicate J true) (h104 : s 104=List.replicate W false)
    (he : ∀ i ∈ targetScratch, s i=[]) :
    ExecutesIn initializeTarget (targetBudget s J W) s (targetState s J W) := by
  let s1 := Function.update (Function.update s 237 (s 193)) 193 (s 213)
  let s2 := Function.update (Function.update s1 238 (s 243)) 243 (s 213)
  let s3 := constantsState s2 J W
  let s4 := Function.update (Function.update s3 236 (s 192)) 192
    (Counter.paddedBits W (s 207) (s 207) J)
  have e120 := he 120 (by simp [targetScratch])
  have h1 : ExecutesIn (saveReplace 213 193 237)
      (9*(s 193).length+7*J+13) s s1 := by
    simpa [s1,hJ] using saveReplace_run s 213 193 237
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      e120 (he 237 (by simp [targetScratch]))
  have h2 : ExecutesIn (saveReplace 213 243 238)
      (9*(s 243).length+7*J+13) s1 s2 := by
    simpa [s2,s1,hJ] using saveReplace_run s1 213 243 238
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp [s1,e120]) (by simpa [s1] using he 238 (by simp [targetScratch]))
  have h3 : ExecutesIn constructConstants (440*(J+1)*(W+1)+7*W+5) s2 s3 := by
    apply constructConstants_run s2 J W
    · simpa [s2,s1] using hz
    · simpa [s2,s1] using ho
    · simpa [s2,s1] using hx
    · simp [s2,s1,hJ]
    · simpa [s2,s1] using h104
    · intro i hi
      have hi' : i ∈ targetScratch := by
        simp only [constantScratch,List.mem_cons] at hi
        simp only [targetScratch,List.mem_cons]
        tauto
      have hi193 : i≠193 := by intro h; subst i; simp [constantScratch] at hi
      have hi237 : i≠237 := by intro h; subst i; simp [constantScratch] at hi
      have hi238 : i≠238 := by intro h; subst i; simp [constantScratch] at hi
      have hi243 : i≠243 := by intro h; subst i; simp [constantScratch] at hi
      simpa [s2,s1,hi193,hi237,hi238,hi243] using he i hi'
  have h4 : ExecutesIn (saveReplace 239 192 236)
      (9*(s 192).length+7*(J*W)+13) s3 s4 := by
    simpa [s4,s3,constantsState,s2,s1,
      Counter.paddedBits_length J W (s 207) (s 207) hz hz] using
      saveReplace_run s3 239 192 236 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by simp [s3,constantsState,s2,s1,e120])
        (by simpa [s3,constantsState,s2,s1] using he 236 (by simp [targetScratch]))
  have hout : Function.update s4 239 []=targetState s J W := by
    funext i
    by_cases h192 : i=192
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    by_cases h193 : i=193
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    by_cases h236 : i=236
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    by_cases h237 : i=237
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    by_cases h238 : i=238
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    by_cases h239 : i=239
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1,he 239 (by simp [targetScratch])]
    by_cases h243 : i=243
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    by_cases h247 : i=247
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    by_cases h254 : i=254
    · subst i
      simp [targetState,s4,s3,constantsState,s2,s1]
    simp [targetState,s4,s3,constantsState,s2,s1,
      h192,h193,h236,h237,h238,h239,h243,h247,h254]
  have h5 : ExecutesIn (clear 239) (2*(J*W)+3) s4 (targetState s J W) := by
    have h := clear_run 239 s4
    rw [hout] at h
    simpa [s4,s3,constantsState,s2,s1,
      Counter.paddedBits_length J W (s 207) (s 207) hz hz] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have hcost : (9 * (s 193).length + 7 * J + 13) +
      ((9 * (s 243).length + 7 * J + 13) +
        ((440 * (J + 1) * (W + 1) + 7 * W + 5) +
          ((9 * (s 192).length + 7 * (J * W) + 13) + (2 * (J * W) + 3)))) =
      targetBudget s J W := by
    simp only [targetBudget]
    omega
  rw [← hcost]
  exact h

/-- Restore all three original caches and release the point and scalar zero. -/
def finishTarget : Code := .seq (restoreCache 192 236)
  (.seq (restoreCache 193 237) (.seq (restoreCache 243 238)
    (.seq (clear 247) (clear 254))))


def finishedTarget (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update s
      236 []) 192 (s 236)) 237 []) 193 (s 237)) 238 []) 243 (s 238)) 247 []) 254 []

theorem finishTarget_run (s : Store) (h245 : s 245=[]) :
    ExecutesIn finishTarget
      (2*((s 192).length+(s 193).length+(s 243).length+(s 247).length+(s 254).length)+
        6*((s 236).length+(s 237).length+(s 238).length)+33)
      s (finishedTarget s) := by
  let s1 := Function.update (Function.update s 236 []) 192 (s 236)
  let s2 := Function.update (Function.update s1 237 []) 193 (s 237)
  let s3 := Function.update (Function.update s2 238 []) 243 (s 238)
  let s4 := Function.update s3 247 []
  have h1 : ExecutesIn (restoreCache 192 236)
      (2*(s 192).length+6*(s 236).length+9) s s1 :=
    restoreCache_run s 192 236 (by decide) (by decide) (by decide) h245
  have h2 : ExecutesIn (restoreCache 193 237)
      (2*(s 193).length+6*(s 237).length+9) s1 s2 := by
    simpa [s2,s1] using restoreCache_run s1 193 237
      (by decide) (by decide) (by decide) (by simp [s1,h245])
  have h3 : ExecutesIn (restoreCache 243 238)
      (2*(s 243).length+6*(s 238).length+9) s2 s3 := by
    simpa [s3,s2,s1] using restoreCache_run s2 243 238
      (by decide) (by decide) (by decide) (by simp [s2,s1,h245])
  have h4 : ExecutesIn (clear 247) (2*(s 247).length+3) s3 s4 := by
    simpa [s4,s3,s2,s1] using clear_run 247 s3
  have h5 : ExecutesIn (clear 254) (2*(s 254).length+3) s4 (finishedTarget s) := by
    simpa [finishedTarget,s4,s3,s2,s1] using clear_run 254 s4
  have hcost : (2 * (s 192).length + 6 * (s 236).length + 9) +
      ((2 * (s 193).length + 6 * (s 237).length + 9) +
        ((2 * (s 243).length + 6 * (s 238).length + 9) +
          ((2 * (s 247).length + 3) + (2 * (s 254).length + 3)))) =
      2 * ((s 192).length + (s 193).length + (s 243).length +
        (s 247).length + (s 254).length) +
        6 * ((s 236).length + (s 237).length + (s 238).length) + 33 := by omega
  rw [← hcost]
  exact h1.seq (h2.seq (h3.seq (h4.seq h5)))



theorem targetState_frame (s : Store) (J W : ℕ) (i : Fin 256)
    (hi : i.val < 205) (h192 : i≠192) (h193 : i≠193) :
    targetState s J W i=s i := by
  have h236 : i≠236 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h237 : i≠237 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h238 : i≠238 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h243 : i≠243 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h247 : i≠247 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h254 : i≠254 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp [targetState,h192,h193,h236,h237,h238,h243,h247,h254]

/-- The dictionary may change while the temporary caches are live. Restoring
those caches preserves precisely that completed dictionary. -/
theorem target_restore_dictionary (s : Store) (J W : ℕ) (output : List Bool)
    (he : ∀ i∈targetScratch,s i=[]) :
    finishedTarget (Function.update (targetState s J W) 217 output)=
      Function.update s 217 output := by
  funext i
  by_cases h192 : i=192
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h193 : i=193
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h217 : i=217
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h236 : i=236
  · subst i
    simp [finishedTarget,targetState,he 236 (by simp [targetScratch])

]
  by_cases h237 : i=237
  · subst i
    simp [finishedTarget,targetState,
      he 237 (by simp [targetScratch])
]
  by_cases h238 : i=238
  · subst i
    simp [finishedTarget,targetState,
he 238 (by simp [targetScratch])
]
  by_cases h243 : i=243
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h247 : i=247
  · subst i
    simp [finishedTarget,targetState,

      he 247 (by simp [targetScratch])]
  by_cases h254 : i=254
  · subst i
    simp [finishedTarget,targetState,

he 254 (by simp [targetScratch])]
  simp [finishedTarget,targetState,h192,h193,h217,h236,h237,h238,h243,h247,h254]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
