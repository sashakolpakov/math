import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramBounds

namespace OAI.Algorithms

/-! Explicit polynomial cost of the complete low-variable producer. Incoming
cache size is charged even when the source and target cutoffs differ. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem fixedRows_length {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    (Encoding.encodeList Fixed.encode (rows.map Prod.fst)).length=
      rows.length*(2*(N*(d*B))+2)+1 := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.map_cons,Encoding.length_encodeList_cons,Fixed.encode_length]
      rw [ih]
      simp only [List.length_cons]
      ring

def lowWorkPolynomial (n N J t d E : ℕ) : ℕ :=
  let B := baseWidth 3 t
  let W := d*B
  1000000*(n+1)*(N+1)*(d+1)^3*(B+1)^2 + (33*n+20*W+83) +
  (9*E+14*J+9*(J*W)+7*W+440*(J+1)*(W+1)+47) +
  (7*(n*(2*(N*W)+2)+1)+9*n+n*(rowWorkPolynomial N J n d B+2)+20) +
  (2*(2*(J*W)+2*J+W)+6*E+33) + (2*W+3)

theorem LowInput.budget_bound {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
    (h : LowInput t a M cache J N theta rows s) :
    lowBudget s rows.length N J t d ≤
      lowWorkPolynomial rows.length N J t d
        ((s 192).length+(s 193).length+(s 243).length) := by
  have hL : ∀ row∈pairedRows rows,row.1.length=N := by
    intro row hr
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr
    exact r.1.property
  have hb := PerturbationBetaProgram.runBudget_eq t d N s (pairedRows rows) theta
    (RingProgram.modelProgram t a M cache).zeroRun.1 hL
    (by simpa only [PerturbationBetaProgram.rowsBits,pairedRows_encode] using h.sourceRows)
    (by simpa [pairedRows,List.map_map,Function.comp_def] using h.choices)
    h.zeroWord h.thetaWord h.wordWidth
  simp only [pairedRows,List.length_map] at hb
  have hb' : PerturbationBetaProgram.runBudget s rows.length N t d ≤
      1000000*(rows.length+1)*(N+1)*(d+1)^3*(baseWidth 3 t+1)^2 := by
    rw [hb]
    exact PerturbationBetaProgram.nativeBudget_polynomial rows.length N t d
  have hs : (s 205).length=rows.length*(2*(N*(d*baseWidth 3 t))+2)+1 := by
    rw [h.sourceRows]
    exact fixedRows_length rows
  have hr := shifted_row_work_bound N J rows.length d (baseWidth 3 t)
  change nativeRowBudget N J rows.length (d*baseWidth 3 t)
    (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J) ≤ _ at hr
  have hr' := Nat.mul_le_mul_left rows.length (Nat.add_le_add_right hr 2)
  unfold lowBudget targetBudget lowWorkPolynomial
  rw [hs]
  dsimp only
  omega

/-- Full native execution with the explicit polynomial bound. -/
theorem LowInput.run_polynomial {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
    (h : LowInput t a M cache J N theta rows s) :
    ExecutesIn prepareLow
      (lowWorkPolynomial rows.length N J t d ((s 192).length+(s 193).length+(s 243).length)) s
      (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217))) :=
  h.run.mono h.budget_bound

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
