import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramPaddingSemantics

namespace OAI.Algorithms

/-! Native composition from a complete scalar coefficient row to its shifted
jet. Padding and both runtime counters are executed, rather than supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationProgram
open CRTLocalProgram (ServiceSpec LowFrame serviceSpec_frame)

def shift (multiply add : Code) : Code :=
  .seq loadRow (.seq Padding.command (.seq enterHorner
    (.seq (HornerProgram.command multiply add) (clear 250))))

def shiftBudget (N J W Km Ka : ℕ) : ℕ :=
  (6*(N*W)+7*N+7*W+16) + Padding.budget N J W +
  (6*(N*J*W)+7*N+2*W+14*(J*W)+24) +
  HornerProgram.budget N (J*W) Km Ka + (2*(J*W)+3)

def shiftScratch : List (Fin 256) :=
  [100,101,102,107,108,120,240,241,244,245,246,248,250,251,252,253]

/-- The two services are fixed finite commands. The input is a full scalar
row at219; no pre-padded stream or evaluated/shifted row is a premise. -/
theorem shift_run {C A : Type*} (s : Store) (encC : C → List Bool)
    (encA : A → List Bool) (lift : C → A) (multiply add : Code)
    (mulOp addOp : A → A → A) (Km Ka J W : ℕ)
    (hm : ServiceSpec s encA multiply mulOp Km)
    (ha : ServiceSpec s encA add addOp Ka)
    (hc : ∀ c, (encC c).length=W) (hw : ∀ a, (encA a).length=J*W)
    (hlift : ∀ c, Padding.cell J W (encC c)=encA (lift c))
    (P : List C) (x zero : A)
    (hrow : s 219=HornerProgram.encodePolynomial encC P)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=W)
    (hx : s 247=encA x) (hz : s 192=encA zero)
    (hJ : s 243=List.replicate J true)
    (hzero : s 104=List.replicate W false)
    (h254 : s 254=List.replicate W false)
    (he : ∀ i ∈ shiftScratch, s i=[]) :
    ExecutesIn (shift multiply add) (shiftBudget P.length J W Km Ka) s
      (Function.update (Function.update s 219 []) 240
        (encA (HornerProgram.fold (HornerProgram.stepValue mulOp addOp x)
          (P.map lift).reverse zero))) := by
  have e100 := he 100 (by simp [shiftScratch])
  have e101 := he 101 (by simp [shiftScratch])
  have e102 := he 102 (by simp [shiftScratch])
  have e107 := he 107 (by simp [shiftScratch])
  have e108 := he 108 (by simp [shiftScratch])
  have e120 := he 120 (by simp [shiftScratch])
  have e240 := he 240 (by simp [shiftScratch])
  have e241 := he 241 (by simp [shiftScratch])
  have e244 := he 244 (by simp [shiftScratch])
  have e245 := he 245 (by simp [shiftScratch])
  have e246 := he 246 (by simp [shiftScratch])
  have e248 := he 248 (by simp [shiftScratch])
  have e250 := he 250 (by simp [shiftScratch])
  have e251 := he 251 (by simp [shiftScratch])
  have e252 := he 252 (by simp [shiftScratch])
  have e253 := he 253 (by simp [shiftScratch])
  let s1 := loaded s
  let s2 := Function.update (Function.update (Function.update s1 246 [])
    240 (Padding.output encC J W P)) 248 []
  let s3 := hornerInput s2
  let answer := encA (HornerProgram.fold (HornerProgram.stepValue mulOp addOp x)
    (P.map lift).reverse zero)
  let s4 := Function.update (Function.update (Function.update s3 246 []) 240 answer) 248 []
  have h1 : ExecutesIn loadRow (6*(P.length*W)+7*P.length+7*W+16) s s1 := by
    simpa [s1,hrow,HornerProgram.encodePolynomial_length encC W hc,hcount,hwidth] using
      loadRow_run s e120 e245 e246 e248 e250
  have h2 : ExecutesIn Padding.command (Padding.budget P.length J W) s1 s2 := by
    apply Padding.command_run s1 encC J W hc P
    all_goals simp_all [s1,loaded]
  have hpad : Padding.output encC J W P =
      HornerProgram.encodePolynomial encA (P.map lift) := by
    simp [Padding.output,HornerProgram.encodePolynomial,List.flatMap_map,hlift]
  have h3 : ExecutesIn enterHorner
      (6*(P.length*J*W)+7*P.length+2*W+14*(J*W)+24) s2 s3 := by
    have h := enterHorner_run s2
      (by simp [s2,s1,loaded,e120]) (by simp [s2,s1,loaded,e245])
      (by simp [s2]) (by simp [s2])
    simpa [s3,s2,s1,loaded,Padding.output_length encC J W hc,hcount,hwidth,hz,hw] using h
  have hf : LowFrame s s3 := by
    intro i hi
    have h219 : i≠219 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h240 : i≠240 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h246 : i≠246 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h248 : i≠248 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h250 : i≠250 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    simp [s3,hornerInput,s2,s1,loaded,h219,h240,h246,h248,h250]
  have h4 : ExecutesIn (HornerProgram.command multiply add)
      (HornerProgram.budget P.length (J*W) Km Ka) s3 s4 := by
    have h := HornerProgram.command_run s3 encA multiply add mulOp addOp Km Ka (J*W)
      (serviceSpec_frame hm hf) (serviceSpec_frame ha hf) hw (P.map lift) x zero
      (by simp [s3,hornerInput,s2,hpad]) (by simp [s3,hornerInput,s2,s1,loaded,hx])
      (by simp [s3,hornerInput,s2,s1,loaded,hz])
      (by simp [s3,hornerInput,s2,s1,loaded,hcount])
      (by simp [s3,hornerInput,s2,s1,loaded,hz,hw])
      (by simp [s3,hornerInput,s2,s1,loaded,e120])
      (by simp [s3,hornerInput,s2,s1,loaded,e241])
      (by simp [s3,hornerInput,s2,s1,loaded,e244])
      (by simp [s3,hornerInput,s2,s1,loaded,e245])
      (by simp [s3,hornerInput,s2,s1,loaded,e251])
      (by simp [s3,hornerInput,s2,s1,loaded,e252])
    simpa [s4,answer] using h
  have hout : Function.update s4 250 [] =
      Function.update (Function.update s 219 []) 240 answer := by
    funext i
    by_cases h219 : i=219 <;> by_cases h240 : i=240 <;>
      by_cases h246 : i=246 <;> by_cases h248 : i=248 <;> by_cases h250 : i=250 <;>
      simp [s4,s3,hornerInput,s2,s1,loaded,
        h219,h240,h246,h248,h250,e246,e248,e250]
  have h5 : ExecutesIn (clear 250) (2*(J*W)+3) s4
      (Function.update (Function.update s 219 []) 240 answer) := by
    have h := clear_run 250 s4
    rw [hout] at h
    simpa [s4,s3,hornerInput,s2,s1,loaded,hz,hw] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert h using 1 <;> first
    | rfl
    | omega
    | (simp only [shiftBudget] ; omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
