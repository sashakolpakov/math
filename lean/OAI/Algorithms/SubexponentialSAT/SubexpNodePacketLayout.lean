import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketStage

namespace OAI.Algorithms

/-! Derive packet readiness from the concrete stored inputs and empty work
cells. The hypotheses contain no projected state or execution premise. -/

namespace SubexponentialSAT.SubexpNodePacketLayout

open BitProgram StructuredCalls
open SubexpFactorPacketProgram
open Subexp.FactorPacketCoordinates (cacheBytes)

attribute [local simp] Fin.coe_ofNat_eq_mod

structure Stored (d : Data) (i : Inputs) : Prop where
  origins : d.stacks 227 = Encoding.encodeList (Encoding.encodeList id) i.origins
  columns : d.stacks 102 =
    Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)) i.columns
  scopes : d.stacks 256 =
    Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes i.scopes
  tables : d.stacks 257 = Encoding.encodeList id i.tables
  cache : d.stacks 284 = cacheBytes i.cache
  modulus : d.stacks 128 = i.modulus
  zero : d.stacks 119 = i.zero
  one : d.stacks 120 = i.one
  work : ∀ j : Fin 288, 138 ≤ j.val → j.val < 202 → d.stacks j = []
  groups : d.stacks 224 = []
  output : d.stacks 225 = []

theorem prefix_ready {d : Data} {i : Inputs} (h : Stored d i) :
    projectState registers prefixPorts d =
      SubexpFactorPrefixProgram.inputState (d.regs ∘ registers) i.origins i.columns i.scopes := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext j
    change d.stacks (prefixPorts j) = _
    by_cases h0 : j = 0
    · subst j
      exact h.origins
    by_cases h1 : j = 1
    · subst j
      exact h.columns
    by_cases h2 : j = 2
    · subst j
      exact h.scopes
    by_cases h3 : j = 3
    · subst j
      exact h.groups
    have hj : 4 ≤ j.val := by omega
    have hw := h.work ⟨134 + j.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)
    simpa [prefixPorts, h0, h1, h2, h3, SubexpFactorPrefixProgram.inputState,
      SubexpFactorPrefixProgram.state, SubexpFactorPrefixProgram.store] using hw

theorem packet_ready {d : Data} {i : Inputs} (h : Stored d i) :
    projectState registers packetPorts d =
      SubexpFactorPacketControl.state (d.regs ∘ registers) (initialMasters i) := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext j
    change d.stacks (packetPorts j) = _
    by_cases h40 : j = 40
    · subst j
      exact h.cache
    by_cases h41 : j = 41
    · subst j
      exact h.groups
    by_cases h42 : j = 42
    · subst j
      exact h.tables
    by_cases h43 : j = 43
    · subst j
      exact h.modulus
    by_cases h44 : j = 44
    · subst j
      exact h.zero
    by_cases h45 : j = 45
    · subst j
      exact h.one
    by_cases h47 : j = 47
    · subst j
      exact h.output
    have hw := h.work ⟨138 + j.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)
    simpa [packetPorts, h40, h41, h42, h43, h44, h45, h47,
      SubexpFactorPacketControl.state, SubexpFactorPacketControl.store] using hw

/-- Both actual native calls are ready from the physical byte equations. -/
theorem ready {d : Data} {i : Inputs} (h : Stored d i) :
    SubexpFactorPacketProgram.Ready d i :=
  ⟨prefix_ready h, packet_ready h⟩

end SubexponentialSAT.SubexpNodePacketLayout

end OAI.Algorithms
