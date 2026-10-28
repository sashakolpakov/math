import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateFactors
import OAI.Algorithms.SubexponentialSAT.SubexpTemplatePointServices
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceProgram

namespace OAI.Algorithms

/-! Typed raw template data and the exact output bytes of its concrete
point/factor calls. The data retain ordered lists throughout. -/

namespace SubexponentialSAT.SubexpTemplateData

open SubexpTemplateProgram SubexpSelectedConversions SubexpInputBitProgram
open SubexpTemplatePointServices

abbrev Bits := List Bool

structure Term (p D : ℕ) where
  increment : Fin D → BaseWord p
  support : List (Fin D)
  factors : List (SubexpTemplateFactors.Factor p D)

structure Block (p D : ℕ) where
  base : Fin D → BaseWord p
  support : List (Fin D)
  groups : List (List (Term p D))

def bankBytes {p D : ℕ} (words : Fin D → BaseWord p) : Bits :=
  DensePolynomialLoop.flatten ((List.finRange D).map words)

def supportBytes {D : ℕ} (support : List (Fin D)) : Bits :=
  Encoding.encodeList id (SubexpWeightGather.supportBits support)

def rawTerm {p D : ℕ} (t : Term p D) : SubexpTemplateProgram.Term :=
  ⟨bankBytes t.increment,supportBytes t.support,
    t.factors.map (List.map SubexpBlueprintRows.Row.packet)⟩

def rawBlock {p D : ℕ} (b : Block p D) : SubexpTemplateProgram.Block :=
  ⟨bankBytes b.base,supportBytes b.support,b.groups.map (List.map rawTerm)⟩

def rawFactorBytes {p D : ℕ} (t : Term p D) : Bits :=
  Encoding.encodeList SubexpTemplateFactors.encode t.factors

variable {p D : ℕ} [Fact p.Prime]

structure ContextGood (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1))) : Prop where
  sourceModulus : ctx.sourceModulus = source.modulus.bits
  sourceReduction : ctx.sourceReduction = SubexpQuarticFlatMul.flat source.reduction
  sourceZero : ctx.sourceZero = SubexpQuarticFlatMul.flat source.zero
  sourceWidth : ctx.sourceWidth.length = SubexpLiftRing.baseWidth p 1
  targetWidth : ctx.targetWidth.length = SubexpLiftRing.baseWidth p (D+1)
  targetModulus : ctx.targetModulus = target.modulus.bits
  targetMinusOne : ctx.targetMinusOne = minusOne.val
  dimension : ctx.dimension = D
  indexWidth : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension

theorem ContextGood.forPoint {ctx : Context} {source : Prepared p 0} {target : Prepared p D}
    {minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1))}
    (hc : ContextGood ctx source target minusOne) (point : Fin D → ResidueCode p) :
    SubexpBlueprintCoordinate.ContextGood (SubexpTemplateFactors.contextFor ctx point)
      source target minusOne point :=
  ⟨hc.sourceModulus,hc.sourceReduction,hc.sourceZero,rfl,hc.sourceWidth,hc.targetWidth,
    hc.targetModulus,hc.targetMinusOne,hc.dimension⟩

def point (source : Prepared p 0) (base : Fin D → BaseWord p) (t : Term p D) :
    Fin D → ResidueCode p := quarticPoint p source.modulus base t.increment

def preparedFactors (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (t : Term p D) : List (List SubexpTableSource.Row) :=
  t.factors.map (SubexpTemplateFactors.output ctx source target minusOne (point source base t))

def preparedFactorBytes (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (t : Term p D) : Bits :=
  Encoding.encodeList SubexpTableSource.encodeRows (preparedFactors ctx source target minusOne base t)

def preparedTerm (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (t : Term p D) : SubexpMomentSourceProgram.Term :=
  ⟨⟨pointBank p source.modulus base t.increment,supportBytes t.support⟩,
    preparedFactors ctx source target minusOne base t⟩

def preparedBlock (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (b : Block p D) : SubexpMomentSourceProgram.Block :=
  ⟨⟨bankBytes b.base,supportBytes b.support⟩,
    b.groups.map (List.map (preparedTerm ctx source target minusOne b.base))⟩

/-- Every byte copy and called program contributes linearly to this one
term's measured bound. Factor calls appear once per actual occurrence. -/
def termCost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (t : Term p D) : ℕ :=
  11*(bankBytes t.increment).length+19*(supportBytes t.support).length+
    9*(rawFactorBytes t).length+10*(pointBank p source.modulus base t.increment).length+
    2*(pointStream p source.modulus base t.increment).length+
    SubexpPointBank.steps D (SubexpLiftRing.baseWidth p 1)+
    (2+SubexpTemplateTraversal.bareBudget
      (SubexpTemplateFactors.cost ctx source target minusOne (point source base t)) t.factors)+
    13*(preparedFactorBytes ctx source target minusOne base t).length+
    13*(SubexpMomentSourceProgram.encodeTerm (preparedTerm ctx source target minusOne base t)).length+77

/-- Boundary workspace for a term. The base and enclosing list buffers are
retained; every point/factor/scratch field is empty. -/
def termWork (base input block group outer : Bits) : Work :=
  {base:=base,input:=input,block:=block,group:=group,outer:=outer}

end SubexponentialSAT.SubexpTemplateData

end OAI.Algorithms
