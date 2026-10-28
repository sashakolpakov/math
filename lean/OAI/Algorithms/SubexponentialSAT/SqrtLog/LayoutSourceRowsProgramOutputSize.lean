import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramLength

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem RowProperty.serialized_length {Wit : Type*} (encode : Wit → List Bool)
    (R : ℕ → Wit → Prop) (W j : ℕ) (rows : List Wit)
    (h : RowProperty encode R W j rows) :
    (Encoding.encodeList encode rows).length=rows.length*(2*W+2)+1 := by
  rw [←records_encoding, List.length_append, records_length encode R W j rows h]
  rfl

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
