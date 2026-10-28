import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCanonicalStore
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterFinish
import OAI.Algorithms.SubexponentialSAT.SubexpHornerMachine

namespace OAI.Algorithms

/-! Literal outer inputs and the bridge from its loaded state to the local
correction producer's canonical input. Every nonempty field is either an
external represented input or the output of the checked outer initializer. -/

namespace SubexponentialSAT.SubexpCRTOuterInput

attribute [local simp] Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpPolynomialPowerProgram SubexpCRTOuterProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

def baseContext (t one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) : SubexpCRTCanonicalInput.Context where
  modulus := M.bits
  width := width
  reduction := SubexpFlatAdd.encode t
  exponent := exponent
  one := SubexpFlatAdd.encode one
  minusOne := minusOne.val
  theta := []
  nodes := []
  index := []
  jet := []
  dimension := List.replicate D true
  zero := []

def store {Q : ℕ} (t one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (j : Fin 320) : List Bool :=
  if h : j.val < 256 then
    SubexpCRTCanonicalInput.store (baseContext p D M t one minusOne width exponent)
      ⟨j.val, h⟩
  else if j = 256 then (List.finRange Q).flatMap (fun i => SubexpFlatAdd.encode (nodes i))
  else if j = 265 then (List.finRange Q).flatMap (fun i => encode p (D + 1) (jets i))
  else []

def data {Q : ℕ} (t one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, store p D M t one minusOne width exponent nodes jets⟩

/-- The exact stack state after initialization and loading one node. Its
registers are irrelevant to this representation. -/
def loaded {Q : ℕ} (t one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent binaryD : List Bool) (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (processed remaining : List (Fin Q)) (current : Fin Q) (acc : Coeff p D) :
    Fin 320 → List Bool :=
  sweepStore
    (initializedStacks (data p D M t one minusOne width exponent nodes jets (fun _ => false)) D binaryD)
    (loadedReady (fun i => SubexpFlatAdd.encode (nodes i))
      (fun i => encode p (D + 1) (jets i)) SubexpFlatAdd.encode
      processed remaining current acc)

omit [Fact p.Prime] in
theorem clean {Q : ℕ} (t one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D) :
    ∀ j ∈ initialCleanPorts, store p D M t one minusOne width exponent nodes jets j = [] := by
  intro j hj
  simp only [initialCleanPorts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with h | h
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [store, baseContext, SubexpCRTCanonicalInput.store]
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [store, baseContext, SubexpCRTCanonicalInput.store]

omit [Fact p.Prime] in
theorem loaded_local_store {Q : ℕ} (t one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1)))
    (width exponent binaryD : List Bool) (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (hw : width.length = baseWidth p (D + 1))
    (processed remaining : List (Fin Q)) (current : Fin Q) (acc : Coeff p D)
    (regs : Fin 16 → Bool) :
    (fun j : Fin 256 =>
      sweepStore
        (initializedStacks (data p D M t one minusOne width exponent nodes jets regs) D binaryD)
        (loadedReady (fun i => SubexpFlatAdd.encode (nodes i))
          (fun i => encode p (D + 1) (jets i)) SubexpFlatAdd.encode
          processed remaining current acc) (localPorts j)) =
      SubexpCRTCanonicalInput.canonical p D M t (nodes current) one minusOne width exponent
        (List.ofFn nodes) (List.replicate processed.length false) (jets current) := by
  funext j
  have hn257 : j.val ≠ 257 := by omega
  have hn258 : j.val ≠ 258 := by omega
  have hn259 : j.val ≠ 259 := by omega
  have hn260 : j.val ≠ 260 := by omega
  have hn261 : j.val ≠ 261 := by omega
  have hn266 : j.val ≠ 266 := by omega
  have hn268 : j.val ≠ 268 := by omega
  have hn277 : j.val ≠ 277 := by omega
  by_cases h104 : j.val = 104
  · have hj : j = 104 := Fin.ext h104
    subst j
    simp [sweepStore, initializedStacks, data, store, baseContext, localPorts,
      SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
      SubexpCRTCanonicalInput.context, hw]
  by_cases h213 : j.val = 213
  · have hj : j = 213 := Fin.ext h213
    subst j
    simp [sweepStore, loadedReady, loadedWords, localPorts,
      SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
      SubexpCRTCanonicalInput.context]
  by_cases h214 : j.val = 214
  · have hj : j = 214 := Fin.ext h214
    subst j
    simp [sweepStore, initializedStacks, data, store, baseContext, localPorts,
      SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
      SubexpCRTCanonicalInput.context, List.ofFn_eq_map, List.flatMap_map]
  by_cases h216 : j.val = 216
  · have hj : j = 216 := Fin.ext h216
    subst j
    simp [sweepStore, loadedReady, loadedWords, readyWords, localPorts,
      SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
      SubexpCRTCanonicalInput.context]
  by_cases h225 : j.val = 225
  · have hj : j = 225 := Fin.ext h225
    subst j
    simp [sweepStore, loadedReady, loadedWords, localPorts,
      SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
      SubexpCRTCanonicalInput.context]
  simp [sweepStore, initializedStacks, data, store, baseContext, localPorts,
    SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
    SubexpCRTCanonicalInput.context, Fin.ext_iff,
    hn257, hn258, hn259, hn260, hn261, hn266, hn268, hn277,
    h104, h213, h214, h216, h225, j.isLt]

end SubexponentialSAT.SubexpCRTOuterInput

end OAI.Algorithms
