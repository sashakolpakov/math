import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketCalls

namespace OAI.Algorithms

/-! One actual outer-loop step, including Boolean-row generation. -/

namespace SubexponentialSAT.SubexpFactorPacketLocal

open BitProgram StructuredCalls SubexpScanPrimitives SubexpFactorPacketControl
open SubexpFactorPacketCalls
open Subexp.FactorPacketCoordinates (Prefix cacheBytes)
open Subexp.FactorPacketRows (prefixStream rawRowBytes blueprintRow)
open SubexpFactorRowStream (tableRows)

structure Input where
  prefixes : List Prefix
  answers : Word

def groupBytes (i : Input) : Word := SubexpFactorPrefixProgram.groupBytes i.prefixes

def factorRows (m : Masters) (cache : List (List Word)) (i : Input) :
    List Subexp.FactorBlueprint.Row :=
  (tableRows m.modulus i.prefixes.length m.zero m.one i.answers).map
    (blueprintRow cache i.prefixes)

def factorBytes (m : Masters) (cache : List (List Word)) (i : Input) : Word :=
  Subexp.FactorBlueprint.encodeRows (factorRows m cache i)

def resting (m : Masters) (groups tables acc output : Word) : View :=
  {masters := m, todoGroups := groups, todoTables := tables, acc := acc, output := output}

def groupReadCost (i : Input) : ℕ :=
  9 * (groupBytes i).length + 6 * i.prefixes.length + 9 * (prefixStream i.prefixes).length + 18

def localBudget (m : Masters) (cache : List (List Word)) (i : Input) : ℕ :=
  groupReadCost i + (6 * i.answers.length + 4) +
    SubexpFactorRowStream.runtimeBound m.modulus i.prefixes.length m.zero m.one i.answers +
    Subexp.FactorPacketRows.runtimeBound cache i.prefixes
      (tableRows m.modulus i.prefixes.length m.zero m.one i.answers) +
    (3 * (factorBytes m cache i).length + 3) + (5 * (factorBytes m cache i).length + 7) +
    (2 * i.prefixes.length + 3) + (2 * (prefixStream i.prefixes).length + 3)

theorem makeFactor_eval (regs : Fin 8 → Bool) (m : Masters) (cache : List (List Word))
    (hc : m.cache = cacheBytes cache) (hm : 0 < BinaryArithmetic.toNat m.modulus)
    (hlen : BinaryArithmetic.toNat m.modulus ≤ cache.length)
    (i : Input) (groups tables acc output : Word) :
    ∃ n ≤ localBudget m cache i, ∃ rf,
      Eval makeFactor n
        (workState regs (resting m (Encoding.frame (groupBytes i) ++ groups)
          (Encoding.frame i.answers ++ tables) acc output))
        (workState rf (resting m groups tables
          (true :: (Encoding.frame (factorBytes m cache i) ++ acc)) output)) := by
  let a := resting m (Encoding.frame (groupBytes i) ++ groups)
    (Encoding.frame i.answers ++ tables) acc output
  obtain ⟨r1, h1⟩ := readGroup_eval regs a i.prefixes groups
  let b : View := {a with todoGroups := groups, arity := List.replicate i.prefixes.length true, prefixes := prefixStream i.prefixes}
  obtain ⟨r2, h2⟩ := readTableField_eval r1 b i.answers tables
  let c : View := {b with todoTables := tables, answers := i.answers.reverse}
  obtain ⟨nr, hnr, r3, h3⟩ := rows_eval r2 c i.prefixes.length i.answers
  let rs := tableRows m.modulus i.prefixes.length m.zero m.one i.answers
  let d : View := {c with answers := [], raw := Encoding.encodeList rawRowBytes rs}
  have hv : ∀ row ∈ rs, Subexp.FactorPacketRows.Valid cache i.prefixes row :=
    SubexpFactorRowStream.tableRows_valid m.modulus i.prefixes.length m.zero m.one
      i.answers cache i.prefixes hm hlen rfl
  obtain ⟨nf, hnf, r4, h4⟩ := factor_eval r3 d cache i.prefixes rs hc hv
  let e : View := {d with raw := [], packet := factorBytes m cache i}
  have h5 := movePacket_eval r4 e (factorBytes m cache i).reverse
  simp only [List.reverse_reverse, List.length_reverse] at h5
  let f : View := {e with packet := [], payload := (factorBytes m cache i).reverse}
  have h6 := emitFactor_eval (readRegs r4 0 1 none) f (factorBytes m cache i)
  let r6 := Function.update (Function.update (readRegs r4 0 1 none) 0 true) 1 false
  let g : View := {f with payload := [], acc := true :: (Encoding.frame (factorBytes m cache i) ++ acc)}
  have h7 := clear_arity_eval r6 g
  let h : View := {g with arity := []}
  have h8 := clear_prefixes_eval (readRegs r6 0 1 none) h
  have hall := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨_, ?_, readRegs (readRegs r6 0 1 none) 0 1 none, hall⟩
  change nr ≤ SubexpFactorRowStream.runtimeBound m.modulus i.prefixes.length m.zero m.one i.answers at hnr
  change nf ≤ Subexp.FactorPacketRows.runtimeBound cache i.prefixes
    (tableRows m.modulus i.prefixes.length m.zero m.one i.answers) at hnf
  simp only [localBudget, groupReadCost, groupBytes, g, f, e, d, c, b, h,
    List.length_replicate]
  omega

end SubexponentialSAT.SubexpFactorPacketLocal

end OAI.Algorithms
