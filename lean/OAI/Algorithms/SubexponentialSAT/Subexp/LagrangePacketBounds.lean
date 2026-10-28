import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LagrangePacketBinary

namespace OAI.Algorithms

/-! Explicit input-size bounds for the actual packet programs. -/

namespace SubexponentialSAT.Subexp.LagrangePacketProgram

theorem cost_linear (before : List Word) (coefficients : Word) (after : List Word)
    (saved : Word) :
    cost before coefficients after saved ≤
      50 * (ProgramEncoding.encodeRecords (before ++ coefficients :: after)).length +
        21 * saved.length + 60 := by
  simp only [cost, skipCost, SelectorPairProgram.frameCost, SelectorPairProgram.payload,
    List.length_append, Encoding.length_frame, ProgramEncoding.encodeRecords_length,
    List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.length_cons]
  omega

theorem before_length_le_bytes (before : List Word) (coefficients : Word) (after : List Word) :
    before.length ≤ (ProgramEncoding.encodeRecords (before ++ coefficients :: after)).length := by
  simp only [ProgramEncoding.encodeRecords_length, List.length_append, List.length_cons]
  omega

end SubexponentialSAT.Subexp.LagrangePacketProgram

namespace SubexponentialSAT.Subexp.LagrangePacketBinary

open LagrangePacketProgram

theorem cost_polynomial (before : List Word) (coefficients : Word) (after : List Word)
    (saved bits : Word) (hi : CounterPrograms.value bits = before.length) :
    cost before coefficients after saved bits ≤
      32 * ((ProgramEncoding.encodeRecords (before ++ coefficients :: after)).length + 1) *
          (bits.length + 1) +
        50 * (ProgramEncoding.encodeRecords (before ++ coefficients :: after)).length +
        21 * saved.length + 61 := by
  have hc := LagrangePacketProgram.cost_linear before coefficients after saved
  have hn := LagrangePacketProgram.before_length_le_bytes before coefficients after
  have hb : CounterConversions.runtimeBound bits ≤
      32 * ((ProgramEncoding.encodeRecords (before ++ coefficients :: after)).length + 1) *
        (bits.length + 1) := by
    unfold CounterConversions.runtimeBound
    rw [hi]
    gcongr
  unfold cost
  omega

end SubexponentialSAT.Subexp.LagrangePacketBinary

end OAI.Algorithms
