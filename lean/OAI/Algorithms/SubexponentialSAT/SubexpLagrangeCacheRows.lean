import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheControl

namespace OAI.Algorithms

/-! Actual relocation of the coefficient encoder into the cache controller. -/

namespace SubexponentialSAT.SubexpLagrangeCacheRows

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLagrangeCacheControl

def rowOutput (s : Store) (row : List (List Bool)) (cache : List (List (List Bool))) : Store :=
  Function.update (Function.update s 240 []) 250
    (Subexp.FactorPacketCoordinates.cacheBytes (row :: cache))

theorem writeRow_run (s : Store) (width : List Bool) (row : List (List Bool))
    (cache : List (List (List Bool)))
    (hrow : ∀ w ∈ row, w.length = width.length)
    (hinput : s 240 = row.flatten) (hwidth : s 104 = width)
    (hcount : s 243 = List.replicate row.length true)
    (hcache : s 250 = Subexp.FactorPacketCoordinates.cacheBytes cache)
    (htmp : s 120 = [])
    (hwork : ∀ k ∈ ([226, 229, 230, 231, 232, 233, 234, 235] : List (Fin 256)), s k = []) :
    ExecutesIn writeRow (7 * row.length + SubexpLagrangeCacheEncoding.rowCost width row + 6)
      s (rowOutput s row cache) := by
  have h229 : s 229 = [] := hwork 229 (by simp)
  let ready := Function.update s 229 (List.replicate row.length true)
  have hc : ExecutesIn (copy 243 229) (7 * row.length + 5) s ready := by
    simpa [ready, hcount, h229] using copy_run 243 229 s
      (by decide) (by decide) (by decide) htmp
  intro regs
  obtain ⟨nc, rc, hnc, hcopy⟩ := hc regs
  let caller : SubexpLagrangeCacheControl.Data := ⟨rc, ready⟩
  let localRegs := rc ∘ fiveRegisters
  obtain ⟨rf, htrace⟩ := SubexpLagrangeCacheEncoding.program_trace localRegs width row cache hrow
  have he := eval_call_lifted SubexpLagrangeCacheEncoding.program fiveRegisters rowPorts caller
    fiveRegisters.injective rowPorts.injective htrace
  have hstart : embedState fiveRegisters rowPorts caller
      (SubexpLagrangeCacheEncoding.state localRegs row.flatten width
        (List.replicate row.length true) [] (Subexp.FactorPacketCoordinates.cacheBytes cache) []) =
      caller := by
    apply embedState_eq_of_ports _ _ _ _ _ fiveRegisters.injective rowPorts.injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i
      have hw0 := hwork 226 (by simp)
      have hw1 := hwork 230 (by simp)
      have hw2 := hwork 231 (by simp)
      have hw3 := hwork 232 (by simp)
      have hw4 := hwork 233 (by simp)
      have hw5 := hwork 234 (by simp)
      have hw6 := hwork 235 (by simp)
      fin_cases i <;> simp [caller, ready, rowPorts, SubexpLagrangeCacheEncoding.state,
        SubexpLagrangeCacheEncoding.tapes, hinput, hwidth, hcache, hw0, hw1, hw2,
        hw3, hw4, hw5, hw6]
    · intro i hi; rfl
  let finalRegs := Function.extend fiveRegisters rf rc
  have hfinish : embedState fiveRegisters rowPorts caller
      (SubexpLagrangeCacheEncoding.state rf [] width [] []
        (Subexp.FactorPacketCoordinates.cacheBytes (row :: cache)) []) =
      (⟨finalRegs, rowOutput s row cache⟩ : SubexpLagrangeCacheControl.Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ fiveRegisters.injective rowPorts.injective
    · intro i
      exact fiveRegisters.injective.extend_apply rf rc i
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i
      have hw0 := hwork 226 (by simp)
      have hw1 := hwork 230 (by simp)
      have hw2 := hwork 231 (by simp)
      have hw3 := hwork 232 (by simp)
      have hw4 := hwork 233 (by simp)
      have hw5 := hwork 234 (by simp)
      have hw6 := hwork 235 (by simp)
      fin_cases i <;> simp [rowOutput, rowPorts, SubexpLagrangeCacheEncoding.state,
        SubexpLagrangeCacheEncoding.tapes, hwidth, h229, hw0, hw1, hw2, hw3, hw4, hw5, hw6]
    · intro i hi
      have h240 : i ≠ 240 := fun h => hi ⟨0, h.symm⟩
      have h229' : i ≠ 229 := fun h => hi ⟨3, h.symm⟩
      have h250 : i ≠ 250 := fun h => hi ⟨9, h.symm⟩
      simp [rowOutput, caller, ready, h240, h229', h250]
  rw [hstart, hfinish] at he
  refine ⟨nc + (SubexpLagrangeCacheEncoding.rowCost width row + 1), finalRegs, ?_, hcopy.seq he⟩
  omega

theorem rowCost_le (width : List Bool) (row : List (List Bool))
    (hrow : ∀ w ∈ row, w.length = width.length) :
    7 * row.length + SubexpLagrangeCacheEncoding.rowCost width row + 6 ≤
      100 * (row.length + 1) * (width.length + 1) := by
  have he := Encoding.length_encodeList_upper id row width.length (by
    intro w hw
    exact le_of_eq (hrow w hw))
  unfold SubexpLagrangeCacheEncoding.rowCost
  nlinarith

end SubexponentialSAT.SubexpLagrangeCacheRows

end OAI.Algorithms
