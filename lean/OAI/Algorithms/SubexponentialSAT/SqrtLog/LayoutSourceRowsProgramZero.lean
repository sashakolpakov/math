import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace OAI.Algorithms

/-! Absent factor incidences have zero source polynomials. This branch copies
the initialized zero array once per ambient coordinate and emits every row. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def zeroRow : Code := copy 192 240
def zeroRows : Code := rowsCommand zeroRow

theorem zeroRow_spec (base : Store) (bits : List Bool) (N : ℕ)
    (hz : base 192=bits) (h240 : base 240=[]) (h339 : base 339=[]) :
    RowSpec zeroRow base (fun _ => bits) N (7*bits.length+5) := by
  intro j _ remaining acc
  have h := copy_run 192 240 (rowState base j remaining acc)
    (by decide) (by decide) (by decide) (by simpa [rowState] using h339)
  simpa [zeroRow,rowState,hz,h240] using h

theorem constantRows_encoding (bits : List Bool) (j N : ℕ) :
    rowBytes (fun _ => bits) j N++[false]=Encoding.encodeList id (List.replicate N bits) := by
  rw [←records_encoding]
  have h : (List.range' j N).map (fun _ => bits)=List.replicate N bits := by simp
  rw [←h]
  simp [records,rowBytes]
  induction N with
  | zero => rfl
  | succ N ih => simp [List.replicate_succ,ih]

theorem zeroRows_run (base : Store) (bits : List Bool) (N : ℕ)
    (hz : base 192=bits) (hN : (base 212).length=N)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (h320 : base 320=[]) (h331 : base 331=[]) (h332 : base 332=[])
    (h205 : base 205=[]) (h339 : base 339=[]) :
    ExecutesIn zeroRows (N*(26*bits.length+44)+18) base
      (Function.update base 205 (Encoding.encodeList id (List.replicate N bits))) := by
  have hr := rowsCommand_run zeroRow base (fun _ => bits) N (7*bits.length+5) bits.length
    (zeroRow_spec base bits N hz h240 h339) (fun _ => rfl) hN
    h240 h330 h334 h320 h331 h332 h205 h339
  have hc : 7*bits.length+5+19*bits.length+39=26*bits.length+44 := by omega
  simpa [zeroRows,constantRows_encoding,hc] using hr

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
