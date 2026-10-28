import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginMap
import OAI.Algorithms.SubexponentialSAT.SubexpOriginCacheSemantics

namespace OAI.Algorithms

/-! The concrete current-node Taylor cache is copied and traversed by the
fixed origin program. Its output contains computed source residues, with
all other native stacks preserved. -/

namespace SubexponentialSAT.SubexpOriginExecution

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpOriginControl SubexpOriginCacheSemantics

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)
variable (R N : ℕ) (hN : 0 < N)
variable (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length = baseWidth p 1)

theorem program_runs (hμ : 0 < μ) (inputWidth : List Bool)
    (hB : inputWidth.length = baseWidth p μ) (C : ℕ)
    (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (hC : ∀ incidence ∈ es, incidence.length ≤ C)
    (d : Data) (hi : SubexpOriginMap.incidenceInvariant M.bits inputWidth width d)
    (hm : d.stacks 14 = taylorBytes p μ source target reduction theta R N es)
    (h15 : d.stacks 15 = []) (h16 : d.stacks 16 = [])
    (h23 : d.stacks 23 = []) (h24 : d.stacks 24 = []) :
    ∃ regs : Fin 14 → Bool,
      RunsIn program
        (SubexpOriginMap.tableBound es.length C (baseWidth p μ) (baseWidth p 1)
          M.bits.length (N - 1))
        (d.withPC (some program.entry))
        ((⟨regs, Function.update d.stacks 24
          (Encoding.encodeList (Encoding.encodeList SubexpFlatLift.encode)
            (origins p μ source target reduction theta R N hN M width hw es))⟩ : Data).withPC none) := by
  let rows := cacheRows p μ source target reduction theta R N hN es
  have hBpos : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.succ_pos _)
  have hC' : ∀ coordinates ∈ rows, coordinates.length ≤ C := by
    intro coordinates hc
    obtain ⟨incidence, hi, rfl⟩ := List.mem_map.mp hc
    simpa only [List.length_map] using hC incidence hi
  have hR' : ∀ coordinates ∈ rows, ∀ row ∈ coordinates, row.2.length ≤ N - 1 := by
    intro coordinates hc row hr
    obtain ⟨incidence, hi, rfl⟩ := List.mem_map.mp hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    exact (cacheRow_tail_length p μ source target reduction theta R N hN e).le
  have hm' : d.stacks 14 = inputBytes rows := by
    rw [inputBytes_cacheRows]
    exact hm
  obtain ⟨regs, ht⟩ := SubexpOriginMap.program_runsIn p M width hw hBpos inputWidth hB
    C (N - 1) rows hC' hR' d hi hm' h15 h16 h23 h24
  have hlen : rows.length = es.length := by
    simp only [rows, cacheRows, List.length_map]
  have hout : outputBytes p M width hw rows =
      Encoding.encodeList (Encoding.encodeList SubexpFlatLift.encode)
        (origins p μ source target reduction theta R N hN M width hw es) :=
    outputBytes_cacheRows p μ source target reduction theta R N hN M width hw es
  refine ⟨regs, ?_⟩
  simpa only [hlen, hout] using ht

end SubexponentialSAT.SubexpOriginExecution

end OAI.Algorithms
