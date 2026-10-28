import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateData

namespace OAI.Algorithms

/-!
# Actual template-term preparation

Each term captures its increment and support, calls the finite PointBank
program, prepares every raw factor, and frames the resulting term bytes.
The base and the enclosing block, group, and outer buffers are preserved.
-/

namespace SubexponentialSAT.SubexpTemplateTerms

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpTemplateProgram SubexpTemplatePacking SubexpTemplateTraversal
open SubexpTemplatePointServices SubexpTemplateData
open SubexpSelectedConversions SubexpInputBitProgram

abbrev Bits := List Bool

theorem rawTerm_encode {p D : ℕ} (t : SubexpTemplateData.Term p D) :
    SubexpTemplateProgram.encodeTerm (rawTerm t) =
      Encoding.frame (bankBytes t.increment) ++ Encoding.frame (supportBytes t.support) ++
        Encoding.frame (rawFactorBytes t) := by
  simp only [SubexpTemplateProgram.encodeTerm,rawTerm,rawFactorBytes,
    SubexpBlueprintRows.encodeList_map]
  rfl

variable {p D : ℕ} [Fact p.Prime]

theorem preparedFactorBytes_eq (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (t : SubexpTemplateData.Term p D) :
    SubexpTemplateFactors.records ctx source target minusOne (point source base t) t.factors ++ [false] =
      preparedFactorBytes ctx source target minusOne base t := by
  unfold preparedFactorBytes preparedFactors SubexpTemplateFactors.records
  rw [SubexpBlueprintRows.encodeList_map,SubexpBlueprintRows.encodeList_eq_records]
  rfl

theorem preparedTerm_encode (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (t : SubexpTemplateData.Term p D) :
    Encoding.frame (pointBank p source.modulus base t.increment) ++
        Encoding.frame (supportBytes t.support) ++
        Encoding.frame (preparedFactorBytes ctx source target minusOne base t) =
      SubexpMomentSourceProgram.encodeTerm (preparedTerm ctx source target minusOne base t) := by
  simp only [SubexpMomentSourceProgram.encodeTerm,SubexpMomentSourceProgram.encodeDescriptor,
    preparedTerm,preparedFactorBytes,List.append_assoc]

/-- One real term-body execution, with its measured byte and subroutine cost.
No prepared factor or point stream is assumed as an input. -/
theorem termBody_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p)
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (t : SubexpTemplateData.Term p D) (regs : Fin 8 → Bool)
    (rest block group outer : Bits) :
    ∃ n rf, n ≤ termCost ctx source target minusOne base t ∧
      Eval SubexpTemplateProgram.termBody n
        (state ctx regs (termWork (bankBytes base)
          (SubexpTemplateProgram.encodeTerm (rawTerm t) ++ rest) block group outer))
        (state ctx rf (termWork (bankBytes base) rest block
          ((record (SubexpMomentSourceProgram.encodeTerm
            (preparedTerm ctx source target minusOne base t))).reverse ++ group) outer)) := by
  let I := bankBytes t.increment
  let S := supportBytes t.support
  let F := rawFactorBytes t
  let B := pointBank p source.modulus base t.increment
  let P := pointStream p source.modulus base t.increment
  let C := SubexpTemplateFactors.records ctx source target minusOne (point source base t) t.factors
  let E := preparedFactorBytes ctx source target minusOne base t
  let T := SubexpMomentSourceProgram.encodeTerm (preparedTerm ctx source target minusOne base t)
  let descriptor := Encoding.frame B ++ Encoding.frame S
  let w0 := termWork (bankBytes base)
    (Encoding.frame I ++ (Encoding.frame S ++ (Encoding.frame F ++ rest))) block group outer
  have hI := capture_field ctx regs w0 .increment (by decide) (by decide) I
    (Encoding.frame S ++ (Encoding.frame F ++ rest)) rfl rfl rfl
  let r1 := readRegs regs 0 1 none
  let w1 : Work := {w0 with input:=Encoding.frame S ++ (Encoding.frame F ++ rest),increment:=I}
  have hS := capture_field ctx r1 w1 .support (by decide) (by decide) S
    (Encoding.frame F ++ rest) rfl rfl rfl
  let r2 := readRegs r1 0 1 none
  let w2 : Work := {w1 with input:=Encoding.frame F ++ rest,support:=S}
  have hU := unframe_work ctx r2 w2 F rest rfl
  let r3 := readRegs r2 0 1 none
  let w3 : Work := {w2 with input:=F ++ rest}
  obtain ⟨np,rp,hnp,hP⟩ := point_eval p source.modulus base t.increment ctx r3 w3
    hc.sourceModulus hc.sourceWidth rfl rfl rfl rfl
  let w4 : Work := {w3 with bank:=B,point:=P}
  have hBF := appendFrame_field ctx rp w4 .bank .term
    (by decide) (by decide) (by decide) rfl
  let r4 := afterFrameRegs rp
  change Eval (appendFrame 138 133) (8*B.length+7) (state ctx rp w4)
    (state ctx r4 {w4 with term:=(Encoding.frame B).reverse ++ []}) at hBF
  simp only [List.append_nil] at hBF
  let w5 : Work := {w4 with term:=(Encoding.frame B).reverse}
  have hBC := clear_field ctx r4 w5 .bank
  let r5 := readRegs r4 0 1 none
  let w6 : Work := {w5 with bank:=[]}
  have hSF := appendFrame_field ctx r5 w6 .support .term
    (by decide) (by decide) (by decide) rfl
  let r6 := afterFrameRegs r5
  have hdesc : (Encoding.frame S).reverse ++ (Encoding.frame B).reverse = descriptor.reverse := by
    simp only [descriptor,List.reverse_append]
  change Eval (appendFrame 129 133) (8*S.length+7) (state ctx r5 w6)
    (state ctx r6 {w6 with term:=(Encoding.frame S).reverse ++ (Encoding.frame B).reverse}) at hSF
  rw [hdesc] at hSF
  let w7 : Work := {w6 with term:=descriptor.reverse}
  have hSC := clear_field ctx r6 w7 .support
  let r7 := readRegs r6 0 1 none
  let w8 : Work := {w7 with support:=[]}
  obtain ⟨nf,rf,hnf,hF⟩ := SubexpTemplateFactors.factors_eval ctx source target minusOne
    (point source base t) (hc.forPoint (point source base t)) hc.indexWidth
    t.factors r7 w8 rest rfl rfl rfl rfl
  change Eval (scanBare factorBody) nf (state ctx r7 w8)
    (state ctx rf {w8 with input:=rest,factors:=C.reverse ++ []}) at hF
  simp only [List.append_nil] at hF
  let w9 : Work := {w8 with input:=rest,factors:=C.reverse}
  have hFP := push_field ctx rf w9 .factors false
  let r8 := Function.update rf 0 false
  let w10 : Work := {w9 with factors:=false :: C.reverse}
  have hFT := transfer_field ctx r8 w10 .factors .payload (by decide)
  let r9 := readRegs r8 0 1 none
  have hE : (false :: C.reverse).reverse = E := by
    simpa only [List.reverse_cons,List.reverse_reverse,C,E] using
      preparedFactorBytes_eq ctx source target minusOne base t
  change Eval (transfer 134 135) (3*(false :: C.reverse).length+3) (state ctx r8 w10)
    (state ctx r9 {w10 with factors:=[],payload:=(false :: C.reverse).reverse ++ []}) at hFT
  rw [hE,List.append_nil] at hFT
  let w11 : Work := {w10 with factors:=[],payload:=E}
  have hFF := appendFrame_field ctx r9 w11 .payload .term
    (by decide) (by decide) (by decide) rfl
  let r10 := afterFrameRegs r9
  have hT : (Encoding.frame E).reverse ++ descriptor.reverse = T.reverse := by
    dsimp only [T]
    rw [←preparedTerm_encode ctx source target minusOne base t]
    simp only [descriptor,B,S,E,List.reverse_append,List.append_assoc]
  change Eval (appendFrame 135 133) (8*E.length+7) (state ctx r9 w11)
    (state ctx r10 {w11 with term:=(Encoding.frame E).reverse ++ descriptor.reverse}) at hFF
  rw [hT] at hFF
  let w12 : Work := {w11 with term:=T.reverse}
  have hFC := clear_field ctx r10 w12 .payload
  let r11 := readRegs r10 0 1 none
  let w13 : Work := {w12 with payload:=[]}
  have hPC := clear_field ctx r11 w13 .point
  let r12 := readRegs r11 0 1 none
  let w14 : Work := {w13 with point:=[]}
  have hIC := clear_field ctx r12 w14 .increment
  let r13 := readRegs r12 0 1 none
  let w15 : Work := {w14 with increment:=[]}
  have hPack := packComplete_field ctx r13 w15 .term .group
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
  have h := hI.seq (hS.seq (hU.seq (hP.seq (hBF.seq (hBC.seq (hSF.seq (hSC.seq
    (hF.seq ((hFP.seq (hFT.seq (hFF.seq hFC))).seq (hPC.seq (hIC.seq hPack)))))))))))
  refine ⟨_,afterFrameRegs r13,?_,by
    simpa only [SubexpTemplateProgram.termBody,finishFactors,rawTerm_encode,
      List.append_assoc,inputState,termWork,pointWork,put,fieldValue,Field.port,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,
      I,S,F,B,P,C,E,T,descriptor,List.append_nil,List.reverse_reverse] using h⟩
  have hlen := congrArg List.length hE
  simp only [List.length_reverse,List.length_cons] at hlen
  dsimp only [termCost]
  simp only [List.length_reverse,List.length_cons]
  dsimp only [I,S,F,B,P,C,E,T] at hlen ⊢
  omega

end SubexponentialSAT.SubexpTemplateTerms

end OAI.Algorithms
