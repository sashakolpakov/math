import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintTraversal
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintArgumentServices
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorBlueprint

namespace OAI.Algorithms

/-! A raw coordinate packet is consumed by the actual beta and Ce programs.
The output byte string is computed from those programs' physical outputs;
neither a Ce literal nor a source expression is a premise. -/

namespace SubexponentialSAT.SubexpBlueprintCoordinate

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpBlueprintFactor SubexpBlueprintPacking SubexpBlueprintTraversal
open SubexpBlueprintBetaServices SubexpBlueprintArgumentServices
open SubexpInputBitProgram SubexpSelectedConversions SubexpSymbolicCost

abbrev Bits := List Bool

structure Coordinate (p D : ℕ) where
  origin : Fin D → ResidueCode p
  columns : List (List Bits)
  dimension : columns.length = D
  coefficients : List Bits

def Coordinate.packet {p D : ℕ} (c : Coordinate p D) : Subexp.FactorBlueprint.Coordinate where
  origin := (List.finRange D).map (fun i => SubexpQuarticFlatMul.flat (c.origin i))
  taylor := c.columns
  coefficients := c.coefficients

def originBytes {p D : ℕ} (c : Coordinate p D) : Bits :=
  Subexp.FactorBlueprint.originBytes c.packet

def taylorBytes {p D : ℕ} (c : Coordinate p D) : Bits :=
  Subexp.FactorBlueprint.taylorBytes c.packet

def coefficientBytes {p D : ℕ} (c : Coordinate p D) : Bits :=
  Subexp.FactorBlueprint.coefficientBytes c.packet

def incidenceBytes {p D : ℕ} (c : Coordinate p D) : Bits :=
  Encoding.frame (originBytes c) ++ Encoding.frame (taylorBytes c)

def encode {p D : ℕ} (c : Coordinate p D) : Bits :=
  Subexp.FactorBlueprint.encodeCoordinate c.packet

theorem encode_eq {p D : ℕ} (c : Coordinate p D) :
    encode c = Encoding.frame (incidenceBytes c) ++ Encoding.frame (coefficientBytes c) := rfl

theorem originBytes_eq {p D : ℕ} (c : Coordinate p D) :
    originBytes c = Encoding.encodeList SubexpQuarticFlatMul.flat
      ((List.finRange D).map c.origin) := by
  change Encoding.encodeList id
      ((List.finRange D).map (fun i => SubexpQuarticFlatMul.flat (c.origin i))) = _
  simpa only [List.map_map,Function.comp_def] using
    SubexpInputZip.encodeList_map SubexpQuarticFlatMul.flat ((List.finRange D).map c.origin)

theorem taylorBytes_eq {p D : ℕ} (c : Coordinate p D) :
    taylorBytes c = Encoding.encodeList id (SubexpCacheArgument.columnRecords c.columns) := by
  unfold taylorBytes Subexp.FactorBlueprint.taylorBytes Coordinate.packet
  unfold SubexpCacheArgument.columnRecords
  induction c.columns with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,Encoding.encodeList,ih,id_eq]

variable {p D : ℕ} [Fact p.Prime]

/-- These are local identities for runtime masters, each supplied by its
own ring, point-bank, or dimension producer. -/
structure ContextGood (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) : Prop where
  sourceModulus : ctx.sourceModulus = source.modulus.bits
  sourceReduction : ctx.sourceReduction = SubexpQuarticFlatMul.flat source.reduction
  sourceZero : ctx.sourceZero = SubexpQuarticFlatMul.flat source.zero
  pointStream : ctx.pointStream = Encoding.encodeList SubexpQuarticFlatMul.flat
    ((List.finRange D).map point)
  sourceWidth : ctx.sourceWidth.length = SubexpLiftRing.baseWidth p 1
  targetWidth : ctx.targetWidth.length = SubexpLiftRing.baseWidth p (D+1)
  targetModulus : ctx.targetModulus = target.modulus.bits
  targetMinusOne : ctx.targetMinusOne = minusOne.val
  dimension : ctx.dimension = D

def negative (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (c : Coordinate p D) :=
  SubexpQuarticNegMachine.negateWords p (D+1) target.modulus minusOne
    (betaOutput source c.origin point)

def argument (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (c : Coordinate p D) : Bits :=
  SubexpCacheArgument.resultBits
    (SubexpQuarticFlatNeg.flat (betaOutput source c.origin point))
    (SubexpQuarticFlatNeg.flat (negative source target minusOne point c))
    c.columns ctx.indexWidth [false]

def output (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (c : Coordinate p D) : SubexpTableSource.Coordinate :=
  ⟨argument ctx source target minusOne point c,c.coefficients⟩

def betaBudget (ctx : Context) : ℕ :=
  7*ctx.sourceZero.length+7*ctx.pointStream.length+10+sourceSteps D p

def argumentBudget (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (c : Coordinate p D) : ℕ :=
  25000*(SubexpLiftRing.baseWidth p (D+1)+1)^2+
    SubexpCacheArgument.totalCost
      (SubexpQuarticFlatNeg.flat (betaOutput source c.origin point))
      (SubexpQuarticFlatNeg.flat (negative source target minusOne point c))
      c.columns ctx.indexWidth+4

def cost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (c : Coordinate p D) : ℕ :=
  9*(incidenceBytes c).length+7+
  (9*(originBytes c).length+7+
  (9*(taylorBytes c).length+7+
  (9*(coefficientBytes c).length+7+
  (betaBudget (p:=p) (D:=D) ctx+
  (argumentBudget ctx source target minusOne point c+
  (8*(argument ctx source target minusOne point c).length+7+
  (3*(coefficientBytes c).length+3+
  (2*(argument ctx source target minusOne point c).length+3+
  (2*(SubexpQuarticFlatNeg.flat (negative source target minusOne point c)).length+3+
  (2*(SubexpQuarticFlatMul.flat (betaOutput source c.origin point)).length+3+
  (2*(taylorBytes c).length+3+
  (13*(SubexpTableSource.encodeCoordinate (output ctx source target minusOne point c)).length+15))))))))))))

def baseWork (input row factor : Bits) : Work := {input:=input,row:=row,factor:=factor}

/-- One coordinate performs the real arithmetic and serializer calls, then
packs its actual literal and selected coefficient bytes into the row buffer. -/
theorem coordinateBody_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (hc : ContextGood ctx source target minusOne point)
    (c : Coordinate p D) (regs : Fin 8 → Bool) (rest row factor : Bits) :
    ∃ n rf, n ≤ cost ctx source target minusOne point c ∧
      Eval coordinateBody n (state ctx regs (baseWork (encode c ++ rest) row factor))
        (state ctx rf (baseWork rest
          ((record (SubexpTableSource.encodeCoordinate (output ctx source target minusOne point c))).reverse ++ row)
          factor)) := by
  let O := originBytes c
  let T := taylorBytes c
  let C := coefficientBytes c
  let P := incidenceBytes c
  let B := SubexpQuarticFlatMul.flat (betaOutput source c.origin point)
  let N := SubexpQuarticFlatNeg.flat (negative source target minusOne point c)
  let A := argument ctx source target minusOne point c
  let E := SubexpTableSource.encodeCoordinate (output ctx source target minusOne point c)
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  let r4 := readRegs r3 0 1 none
  let w1 := baseWork (P ++ (Encoding.frame C ++ rest)) row factor
  let w2 : Work := {w1 with input:=Encoding.frame T ++ (Encoding.frame C ++ rest),origin:=O}
  let w3 : Work := {w2 with input:=Encoding.frame C ++ rest,taylor:=T}
  let w4 : Work := {w3 with input:=rest,coefficients:=C}
  have hu := unframe_work ctx regs (baseWork [] row factor) P (Encoding.frame C ++ rest) rfl
  have hO := capture_field ctx r1 w1 .origin (by decide) (by decide) O
    (Encoding.frame T ++ (Encoding.frame C ++ rest))
    (by simp only [w1,baseWork,P,incidenceBytes,O,T,List.append_assoc]) rfl rfl
  have hT := capture_field ctx r2 w2 .taylor (by decide) (by decide) T
    (Encoding.frame C ++ rest) rfl rfl rfl
  have hC := capture_field ctx r3 w3 .coefficients (by decide) (by decide) C rest rfl rfl rfl
  obtain ⟨nb,rb,hnb,hB,_⟩ := computeBeta_eval source target c.origin point ctx r4 w4
    hc.sourceModulus hc.sourceReduction hc.sourceZero hc.pointStream (originBytes_eq c)
    hc.sourceWidth hc.targetWidth rfl rfl rfl
  let w5 : Work := {w4 with origin:=[],beta:=B}
  obtain ⟨na,ra,hna,hA⟩ := computeArgument_eval p (D+1) target.modulus
    (betaOutput source c.origin point) minusOne c.columns ctx.indexWidth ctx rb w5
    hc.targetModulus hc.targetMinusOne hc.targetWidth
    (hc.dimension.trans c.dimension.symm) rfl rfl rfl (taylorBytes_eq c) rfl
  let w6 : Work := {w5 with negative:=N,argument:=A}
  have hframe := appendFrame_field ctx ra w6 .argument .coordinate
    (by decide) (by decide) (by decide) rfl
  let r5 := afterFrameRegs ra
  let w7 : Work := {w6 with coordinate:=(Encoding.frame A).reverse}
  change Eval (appendFrame 106 110) (8*A.length+7) (state ctx ra w6)
    (state ctx r5 {w6 with coordinate:=(Encoding.frame A).reverse ++ []}) at hframe
  simp only [List.append_nil] at hframe
  have htransfer := transfer_field ctx r5 w7 .coefficients .coordinate (by decide)
  let r6 := readRegs r5 0 1 none
  let w8 : Work := {w7 with coefficients:=[],coordinate:=E.reverse}
  have he : C.reverse ++ (Encoding.frame A).reverse = E.reverse := by
    simp only [E,output,SubexpTableSource.encodeCoordinate,coefficientBytes,
      Subexp.FactorBlueprint.coefficientBytes,Coordinate.packet,List.reverse_append,A,C]
  change Eval (transfer 105 110) (3*C.length+3) (state ctx r5 w7)
    (state ctx r6 {w7 with coefficients:=[],coordinate:=C.reverse ++ (Encoding.frame A).reverse}) at htransfer
  rw [he] at htransfer
  have hclearA := clear_field ctx r6 w8 .argument
  let r7 := readRegs r6 0 1 none
  let w9 : Work := {w8 with argument:=[]}
  have hclearN := clear_field ctx r7 w9 .negative
  let r8 := readRegs r7 0 1 none
  let w10 : Work := {w9 with negative:=[]}
  have hclearB := clear_field ctx r8 w10 .beta
  let r9 := readRegs r8 0 1 none
  let w11 : Work := {w10 with beta:=[]}
  have hclearT := clear_field ctx r9 w11 .taylor
  let r10 := readRegs r9 0 1 none
  let w12 : Work := {w11 with taylor:=[]}
  have hpack := packComplete_field ctx r10 w12 .coordinate .row
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
  have h := hu.seq (hO.seq (hT.seq (hC.seq (hB.seq (hA.seq
    (hframe.seq (htransfer.seq (hclearA.seq (hclearN.seq (hclearB.seq (hclearT.seq hpack)))))))))))
  refine ⟨_,afterFrameRegs r10,?_,by
    simpa only [coordinateBody,encode_eq,List.append_assoc,inputState,baseWork,
      P,incidenceBytes,O,T,C,B,N,A,E,output,negative,argument,
      SubexpTableSource.encodeCoordinate,coefficientBytes,
      Subexp.FactorBlueprint.coefficientBytes,Coordinate.packet,
      w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,
      betaWork,argumentWork,put,fieldValue,Field.port,List.append_nil,List.reverse_reverse] using h⟩
  dsimp only [cost,betaBudget,argumentBudget]
  simp only [List.length_reverse]
  dsimp only [incidenceBytes,coefficientBytes,argument,negative,output,
    SubexpTableSource.encodeCoordinate,Subexp.FactorBlueprint.coefficientBytes,Coordinate.packet]
  omega

end SubexponentialSAT.SubexpBlueprintCoordinate

end OAI.Algorithms
