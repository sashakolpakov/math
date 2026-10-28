import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyPreparation

namespace OAI.Algorithms

/-! Closed low-variable incidence preparation from physical coefficient rows.
Beta evaluation, point construction, polynomial Horner, sparse emission, and
cache restoration are all performed by fixed finite commands. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- All temporary words of the complete low-variable worker. -/
def lowScratch : List (Fin 256) :=
  PerturbationBetaProgram.workPorts ++ originScratch ++ targetScratch ++
    coordinateLoadScratch ++ shiftScratch ++ coordinateEmitScratch ++ [218,230,231]

def lowBudget (s : Store) (n N J t d : ℕ) : ℕ :=
  PerturbationBetaProgram.runBudget s n N t d + (33*n+20*(d*baseWidth 3 t)+83) +
    targetBudget s J (d*baseWidth 3 t) +
    (7*(s 205).length+9*n+n*(nativeRowBudget N J n (d*baseWidth 3 t)
      (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J)+2)+20) +
    (2*(2*(J*(d*baseWidth 3 t))+2*J+d*baseWidth 3 t)+
      6*((s 192).length+(s 193).length+(s 243).length)+33) +
    (2*(d*baseWidth 3 t)+3)

def pairedRows {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    List (List (Coeff B d) × Bool) := rows.map (fun row => (row.1.val,row.2))

theorem pairedRows_encode {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    Encoding.encodeList (HornerProgram.encodePolynomial RingProgram.flat)
      ((pairedRows rows).map Prod.fst) =
      Encoding.encodeList Fixed.encode (rows.map Prod.fst) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [pairedRows,List.map_cons,Encoding.encodeList] at ih ⊢
      rw [ih]
      simp only [Fixed.encode,DensePolynomialProgram.encode,
        HornerProgram.encodePolynomial,List.flatMap_def]

def lowOutput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (old : List Bool) : List Bool :=
  rowsResult (scanStep (RingProgram.modelProgram t a M cache) J rows.length N theta)
    0 (rows.map Prod.fst)
    (Encoding.frame (originKey rows.length) ++
      Encoding.frame (RingProgram.flat (PerturbationBetaProgram.runValue t a M cache theta
        (pairedRows rows))) ++ old)

private theorem originScratch_ne_betaPort :
    ∀ i : Fin 256, i∈originScratch → i≠220 := by
  intro i hi
  simp [originScratch] at hi
  omega

private theorem targetScratch_ne_seedPorts :
    ∀ i : Fin 256, i∈targetScratch → i≠217 ∧ i≠220 := by
  intro i hi
  simp [targetScratch] at hi
  omega

private theorem scanScratch_ne_targetPorts :
    ∀ i : Fin 256,
      i∈coordinateLoadScratch ++ shiftScratch ++ coordinateEmitScratch ++ [218,230,231] →
      i≠192 ∧ i≠193 ∧ i≠217 ∧ i≠220 ∧ i≠236 ∧ i≠237 ∧ i≠238 ∧
        i≠243 ∧ i≠247 ∧ i≠254 := by
  intro i hi
  simp [coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  omega

theorem prepareLow_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hB : 0 < baseWidth 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (J N : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s scalarWidth frame)
    (Hscalar : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) s)
    (hempty : ∀ i, s (bufferPorts i)=[]) (h121 : s 121=[]) (h122 : s 122=[])
    (hzero : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1 =
      List.replicate (d*baseWidth 3 t) false)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool))
    (hrows : s 205=Encoding.encodeList Fixed.encode (rows.map Prod.fst))
    (hchoice : s 206=rows.map Prod.snd)
    (h207 : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h208 : s 208=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (h209 : s 209=RingProgram.flat theta)
    (h210 : (s 210).length=N) (h211 : (s 211).length=d*baseWidth 3 t)
    (h212 : (s 212).length=rows.length) (h213 : s 213=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth 3 t) false)
    (he : ∀ i∈lowScratch,s i=[]) :
    ExecutesIn prepareLow (lowBudget s rows.length N J t d) s
      (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217))) := by
  let ops := RingProgram.modelProgram t a M cache
  let W := d*baseWidth 3 t
  let beta := PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows)
  let seed := Encoding.frame (originKey rows.length) ++ Encoding.frame (RingProgram.flat beta) ++ s 217
  let b := Function.update s 220 (RingProgram.flat beta)
  let o := Function.update b 217 seed
  let u := targetState o J W
  let out := lowOutput t a M cache J N theta rows (s 217)
  let f := Function.update u 217 out
  have hb : ExecutesIn PerturbationBetaProgram.betaCommand
      (PerturbationBetaProgram.runBudget s rows.length N t d) s b := by
    have h := PerturbationBetaProgram.betaCommand_run t a M cache hz s Hscalar theta
      (pairedRows rows) N
      (by intro row hr; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr; exact r.1.property)
      (by simpa only [PerturbationBetaProgram.rowsBits,pairedRows_encode] using hrows)
      (by simpa [pairedRows,List.map_map,Function.comp_def] using hchoice)
      h207 h209 h210 h211
      (by intro i hi; exact he i (by simp [lowScratch,hi]))
    simpa [b,beta,pairedRows] using h
  have ho : ExecutesIn origin (33*rows.length+20*W+83) b o := by
    have hoScratch : ∀ i∈originScratch,b i=[] := by
      intro i hi
      have hn := originScratch_ne_betaPort i hi
      simpa [b,hn] using he i (by simp [lowScratch,hi])
    simpa [o,b,seed,W] using origin_run b rows.length (by simpa [b] using h212) hoScratch
  have eo : ∀ i∈targetScratch,o i=[] := by
    intro i hi
    have hn := targetScratch_ne_seedPorts i hi
    simpa [o,b,hn.1,hn.2] using he i (by simp [lowScratch,hi])
  have hu : ExecutesIn initializeTarget (targetBudget s J W) o u := by
    have h := initializeTarget_run o J W
      (by simp [o,b,h207,W]) (by simp [o,b,h208,W]) (by simp [o,b,h209,W])
      (by simpa [o,b] using h213) (by simpa [o,b,W] using h104) eo
    simpa [u,targetBudget,o,b] using h
  have uf : ∀ i : Fin 256,i.val < 205 → i≠192 → i≠193 → u i=s i := by
    intro i hi h192 h193
    rw [show u i=o i from targetState_frame o J W i hi h192 h193]
    have h217 : i≠217 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h220 : i≠220 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    simp [o,b,h217,h220]
  have ue : ∀ i∈coordinateLoadScratch ++ shiftScratch ++ coordinateEmitScratch ++ [218,230,231],u i=[] := by
    intro i hi
    have hn := scanScratch_ne_targetPorts i hi
    simpa [u,targetState,o,b,Function.update_apply,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,
      hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.1,
      hn.2.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2.2] using
      he i (by simp only [List.mem_append] at hi ⊢; simp only [lowScratch,List.mem_append]; tauto)
  have hs : ExecutesIn (scanRows coordinate)
      (7*(s 205).length+9*rows.length+rows.length*(nativeRowBudget N J rows.length W
        (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J)+2)+20) u f := by
    have h := native_scan_run 3 t M cache ops (HornerProgram.modelTable t a M cache) hB hz
      (fun _ _ => rfl) (fun _ _ => rfl) u J N scalarWidth frame
      (PairSpec.BaseReady.frame_except_caches 3 t M cache _ H uf)
      (by intro i; rw [uf _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)]; exact hempty i)
      ((uf 121 (by decide) (by decide) (by decide)).trans h121)
      ((uf 122 (by decide) (by decide) (by decide)).trans h122)
      (by simpa [u,targetState,o,b,h207,ops,W] using zero_bits ops.zeroRun.1 hzero J)
      (by simp [u,targetState,o,b,h213]) hzero (rows.map Prod.fst) theta
      (by simpa [u,targetState,o,b] using hrows)
      (by simpa [u,targetState,o,b] using h212)
      (by simpa [u,targetState,o,b] using h210)
      (by simpa [u,targetState,o,b] using h211)
      (by simpa [u,targetState,o,b,h208,h209,ops,W] using point_bits ops.zeroRun.1 ops.oneRun.1 theta hzero J)
      (by simp [u,targetState,o,b,h213])
      (by simpa [u,targetState,o,b] using h213)
      (by simpa [u,targetState,o,b] using h104)
      (by simp [u,targetState,o,b,h207,hzero])
      (by intro i hi; exact ue i (by simp [hi]))
      (by intro i hi; exact ue i (by simp [hi]))
      (by intro i hi; exact ue i (by simp [hi]))
      (ue 230 (by simp)) (ue 231 (by simp)) (ue 218 (by simp))
    simpa [f,out,lowOutput,ops,seed,beta,u,targetState,o,b] using h
  have hf : ExecutesIn finishTarget
      (2*(2*(J*W)+2*J+W)+6*((s 192).length+(s 193).length+(s 243).length)+33)
      f (Function.update o 217 out) := by
    have h := finishTarget_run f (by simpa [f] using ue 245 (by simp [shiftScratch]))
    have hout : finishedTarget f=Function.update o 217 out :=
      target_restore_dictionary o J W out eo
    rw [hout] at h
    have hk : 2*((f 192).length+(f 193).length+(f 243).length+(f 247).length+(f 254).length)+
        6*((f 236).length+(f 237).length+(f 238).length)+33 =
        2*(2*(J*W)+2*J+W)+6*((s 192).length+(s 193).length+(s 243).length)+33 := by
      simp [f,u,targetState,o,b,h213,h207,h208,h209,W,
        DensePolynomialProgram.Constructor.Counter.paddedBits_length]
      ring
    simpa only [hk] using h
  have hc := clear_run 220 (Function.update o 217 out)
  have hout : Function.update (Function.update o 217 out) 220 []=Function.update s 217 out := by
    funext i
    by_cases h217 : i=217
    · subst i; simp
    by_cases h220 : i=220
    · subst i; simp [o,b,he 220 (by simp [lowScratch,PerturbationBetaProgram.workPorts])]
    simp [o,b,h217,h220]
  rw [hout] at hc
  have hc' : ExecutesIn (clear 220) (2*W+3) (Function.update o 217 out)
      (Function.update s 217 out) := by simpa [o,b,W] using hc
  have all := hb.seq (ho.seq (hu.seq (hs.seq (hf.seq hc'))))
  convert all using 1 <;> first | rfl | (simp only [lowBudget,W]; omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
