import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyScan

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def coordinateResult {B d n : ℕ} (ops : RingProgram (Coeff B d)) (J : ℕ)
    (theta : Coeff B d) (v : Fin n) (P : List (Coeff B d)) (acc : List Bool) : List Bool :=
  PerturbationEmitProgram.emitted (Squarefree.encodeMask {v}) 1
    (((shiftedValue ops J theta P).val.map RingProgram.flat).tail) acc

theorem loaded_lowFrame (s : Store) (bits rest mask : List Bool) :
    CRTLocalProgram.LowFrame s (coordinateLoaded s bits rest mask) := by
  intro i hi
  have h214 : i≠214 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h219 : i≠219 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h230 : i≠230 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp [coordinateLoaded,h214,h219,h230]

private theorem shiftScratch_ne_loadPorts :
    ∀ i : Fin 256, i ∈ shiftScratch → i ≠ 214 ∧ i ≠ 219 ∧ i ≠ 230 := by
  intro i hi
  simp [shiftScratch] at hi
  omega

private theorem coordinateEmitScratch_ne_loadPorts :
    ∀ i : Fin 256, i ∈ coordinateEmitScratch → i ≠ 214 ∧ i ≠ 219 ∧ i ≠ 230 := by
  intro i hi
  simp [coordinateEmitScratch] at hi
  omega

/-- This is the complete native coordinate worker: frame decode, physical mask
construction, padding, native polynomial Horner, sparse emission, and cleanup.
There is no shifted-row, padded-input, mask, or coefficient-emission oracle. -/
theorem native_coordinate_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d n : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i)=[])
    (h121 : s 121=[]) (h122 : s 122=[])
    (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
    (hJcount : (s 193).length=J)
    (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
    (P : List (Coeff (baseWidth p t) d)) (theta : Coeff (baseWidth p t) d)
    (v : Fin n) (rest : List Bool)
    (hrow : s 230=true::(Encoding.frame (HornerProgram.encodePolynomial RingProgram.flat P)++rest))
    (hn : (s 212).length=n) (hv : (s 218).length=v.val)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true) (h213 : s 213=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (heLoad : ∀ i ∈ coordinateLoadScratch,s i=[])
    (heShift : ∀ i ∈ shiftScratch,s i=[])
    (heEmit : ∀ i ∈ coordinateEmitScratch,s i=[]) :
    ExecutesIn coordinate
      (15*(P.length*(d*baseWidth p t))+11*n+17*v.val+38+
        shiftBudget P.length J (d*baseWidth p t)
          (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)+
        PerturbationEmitProgram.budget J n (d*baseWidth p t)+2*n+5) s
      (Function.update (Function.update (Function.update s 230 rest)
        217 (coordinateResult ops J theta v P (s 217))) 218 (true::s 218)) := by
  let bits := HornerProgram.encodePolynomial RingProgram.flat P
  let mask := Squarefree.encodeMask {v}
  let s1 := coordinateLoaded s bits rest mask
  let cs := (shiftedValue ops J theta P).val.map RingProgram.flat
  let K := shiftBudget P.length J (d*baseWidth p t)
    (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)
  have hlow := loaded_lowFrame s bits rest mask
  have hsLoad := loadCoordinate_run s v bits rest hrow hn hv heLoad
  have hss : ∀ i ∈ shiftScratch,s1 i=[] := by
    intro i hi
    have hne := shiftScratch_ne_loadPorts i hi
    change Function.update (Function.update (Function.update s 230 rest) 219 bits) 214 mask i = []
    rw [Function.update_noteq hne.1, Function.update_noteq hne.2.1,
      Function.update_noteq hne.2.2]
    exact heShift i hi
  have hse : ∀ i ∈ coordinateEmitScratch,s1 i=[] := by
    intro i hi
    have hne := coordinateEmitScratch_ne_loadPorts i hi
    change Function.update (Function.update (Function.update s 230 rest) 219 bits) 214 mask i = []
    rw [Function.update_noteq hne.1, Function.update_noteq hne.2.1,
      Function.update_noteq hne.2.2]
    exact heEmit i hi
  have hs : ExecutesIn (shift Fixed.mulCommand AddService.command) K s1
      (Function.update (Function.update s1 219 []) 240 (PerturbationEmitProgram.array cs)) := by
    have h := native_shift_run p t M cache ops table hB hz hadd hmul s1 J scalarWidth frame
      (PairSpec.BaseReady.frame p t M cache table H hlow)
      (fun i => (hlow (bufferPorts i) (by fin_cases i <;> decide)).trans (hempty i))
      (by simpa [s1,coordinateLoaded] using h121) (by simpa [s1,coordinateLoaded] using h122)
      (by simpa [s1,coordinateLoaded] using hcache) (by simpa [s1,coordinateLoaded] using hJcount)
      hzero P theta (by simp [s1,coordinateLoaded,bits])
      (by simpa [s1,coordinateLoaded] using hcount) (by simpa [s1,coordinateLoaded] using hwidth)
      (by simpa [s1,coordinateLoaded] using hx) (by simpa [s1,coordinateLoaded] using hJ)
      (by simpa [s1,coordinateLoaded] using h104) (by simpa [s1,coordinateLoaded] using h254) hss
    simpa [K,cs,Fixed.encode,DensePolynomialProgram.encode,PerturbationEmitProgram.array] using h
  have hlen : cs.length=J := by
    simp only [cs, List.length_map, (shiftedValue ops J theta P).property]
  have hm : mask.length=n := by simp [mask,Squarefree.encodeMask]
  have hf := finishCoordinate_run s1 mask (d*baseWidth p t) K cs
    (by intro c hc; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc; exact RingProgram.flat_length a)
    hs (by simpa [s1,coordinateLoaded,hlen] using h213)
    (by simpa [s1,coordinateLoaded] using hwidth) (by simp [s1,coordinateLoaded]) hse
    (hss 240 (by simp [shiftScratch]))
  have hout : Function.update (Function.update (Function.update (Function.update s1 219 [])
      217 (PerturbationEmitProgram.emitted mask 1 cs.tail (s1 217))) 214 []) 218 (true::s1 218) =
      Function.update (Function.update (Function.update s 230 rest)
        217 (coordinateResult ops J theta v P (s 217))) 218 (true::s 218) := by
    funext i
    by_cases h214 : i=214 <;> by_cases h217 : i=217 <;> by_cases h218 : i=218 <;>
      by_cases h219 : i=219 <;> by_cases h230 : i=230 <;>
      first | rfl | simp [s1,coordinateLoaded,coordinateResult,cs,mask,Function.update_apply,
        h214,h217,h218,h219,h230,heLoad 214 (by simp [coordinateLoadScratch]),
        heLoad 219 (by simp [coordinateLoadScratch])]
  rw [hout] at hf
  have h := hsLoad.seq hf
  convert h using 1
  all_goals
    first
    | rfl
    | simp only [bits,HornerProgram.encodePolynomial_length RingProgram.flat
        (d*baseWidth p t) RingProgram.flat_length,hlen,hm,K]
      omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
