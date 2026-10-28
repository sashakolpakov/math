import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeCoordinate

namespace OAI.Algorithms

/-! Complete native coordinate-row scan with arithmetic callbacks discharged. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def scanStep {B d : ℕ} (ops : RingProgram (Coeff B d)) (J n N : ℕ)
    (theta : Coeff B d) (j : ℕ) (P : Fixed.Array B d N) (acc : List Bool) : List Bool :=
  if hj : j < n then coordinateResult ops J theta ⟨j,hj⟩ P.val acc else acc

def nativeRowBudget (N J n W Km Ka : ℕ) : ℕ :=
  15*(N*W)+30*n+43+shiftBudget N J W Km Ka+PerturbationEmitProgram.budget J n W

theorem rowsReady_lowFrame {C : Type*} (s : Store) (encode : C → List Bool)
    (j : ℕ) (cs : List C) (acc count : List Bool) :
    CRTLocalProgram.LowFrame s (rowsReady s encode j cs acc count) := by
  intro i hi
  have h217 : i≠217 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h218 : i≠218 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h230 : i≠230 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h231 : i≠231 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp [rowsReady,h217,h218,h230,h231]

private theorem coordinateLoadScratch_ne_rowsPorts :
    ∀ i : Fin 256, i∈coordinateLoadScratch →
      i≠217 ∧ i≠218 ∧ i≠230 ∧ i≠231 := by
  intro i hi
  simp [coordinateLoadScratch] at hi
  omega

private theorem shiftScratch_ne_rowsPorts :
    ∀ i : Fin 256, i∈shiftScratch →
      i≠217 ∧ i≠218 ∧ i≠230 ∧ i≠231 := by
  intro i hi
  simp [shiftScratch] at hi
  omega

private theorem coordinateEmitScratch_ne_rowsPorts :
    ∀ i : Fin 256, i∈coordinateEmitScratch →
      i≠217 ∧ i≠218 ∧ i≠230 ∧ i≠231 := by
  intro i hi
  simp [coordinateEmitScratch] at hi
  omega

/-- Every row is actually decoded, shifted and emitted by the fixed coordinate
worker. Source lengthN and target lengthJ are independent parameters. -/
theorem native_scan_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J N : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i)=[])
    (h121 : s 121=[]) (h122 : s 122=[])
    (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
    (hJcount : (s 193).length=J)
    (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
    (rows : List (Fixed.Array (baseWidth p t) d N)) (theta : Coeff (baseWidth p t) d)
    (hrows : s 205=Encoding.encodeList Fixed.encode rows)
    (hn : (s 212).length=rows.length)
    (hcount : (s 210).length=N) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true) (h213 : s 213=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (heLoad : ∀ i ∈ coordinateLoadScratch,s i=[])
    (heShift : ∀ i ∈ shiftScratch,s i=[])
    (heEmit : ∀ i ∈ coordinateEmitScratch,s i=[])
    (h230 : s 230=[]) (h231 : s 231=[]) (h218 : s 218=[]) :
    ExecutesIn (scanRows coordinate)
      (7*(s 205).length+9*rows.length+rows.length*
        (nativeRowBudget N J rows.length (d*baseWidth p t)
          (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)+2)+20) s
      (Function.update s 217 (rowsResult (scanStep ops J rows.length N theta) 0 rows (s 217))) := by
  apply scanRows_run s Fixed.encode coordinate (scanStep ops J rows.length N theta)
    _ rows hrows hn (heLoad 120 (by simp [coordinateLoadScratch])) h230 h231 h218
  intro j hj c rest acc count
  let a := rowsReady s (Fixed.encode (J:=N)) j (c::rest) acc count
  let v : Fin rows.length := ⟨j,hj⟩
  have hf := rowsReady_lowFrame s (Fixed.encode (J:=N)) j (c::rest) acc count
  have hl : ∀ i∈coordinateLoadScratch,a i=[] := by
    intro i hi
    have hne := coordinateLoadScratch_ne_rowsPorts i hi
    simpa [a,rowsReady,Function.update_apply,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using heLoad i hi
  have hs : ∀ i∈shiftScratch,a i=[] := by
    intro i hi
    have hne := shiftScratch_ne_rowsPorts i hi
    simpa [a,rowsReady,Function.update_apply,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using heShift i hi
  have he : ∀ i∈coordinateEmitScratch,a i=[] := by
    intro i hi
    have hne := coordinateEmitScratch_ne_rowsPorts i hi
    simpa [a,rowsReady,Function.update_apply,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using heEmit i hi
  have h := native_coordinate_run p t M cache ops table hB hz hadd hmul a J scalarWidth frame
    (PairSpec.BaseReady.frame p t M cache table H hf)
    (fun i => (hf (bufferPorts i) (by fin_cases i <;> decide)).trans (hempty i))
    (by simpa [a,rowsReady] using h121) (by simpa [a,rowsReady] using h122)
    (by simpa [a,rowsReady] using hcache) (by simpa [a,rowsReady] using hJcount)
    hzero c.val theta v (Encoding.encodeList Fixed.encode rest)
    (by simp [a,rowsReady,Encoding.encodeList,Fixed.encode,DensePolynomialProgram.encode,
      HornerProgram.encodePolynomial,List.flatMap_def])
    (by simpa [a,rowsReady] using hn) (by simp [a,rowsReady,v])
    (by simpa [a,rowsReady,c.property] using hcount) (by simpa [a,rowsReady] using hwidth)
    (by simpa [a,rowsReady] using hx) (by simpa [a,rowsReady] using hJ)
    (by simpa [a,rowsReady] using h213) (by simpa [a,rowsReady] using h104)
    (by simpa [a,rowsReady] using h254) hl hs he
  have hout : Function.update (Function.update (Function.update a 230
      (Encoding.encodeList Fixed.encode rest)) 217 (coordinateResult ops J theta v c.val (a 217)))
      218 (true::a 218) =
      rowsReady s Fixed.encode (j+1) rest (scanStep ops J rows.length N theta j c acc) count := by
    funext i
    by_cases h217 : i=217 <;> by_cases h218 : i=218 <;>
      by_cases h230 : i=230 <;> by_cases h231 : i=231 <;>
      simp [a,rowsReady,scanStep,hj,v,Function.update_apply,h217,h218,h230,h231,List.replicate_succ]
  rw [hout] at h
  apply h.mono
  simp only [c.property,nativeRowBudget,v]
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
