import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsNativeCostAlgebra
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramBounds

namespace OAI.Algorithms

/-! Pure numerical expression for the native moment envelope. The bridge
module proves definitional equality with the actual assembly bounds. Keeping
these expressions separate permits checking arithmetic independently of the
large machine-state proof. -/
namespace SubexponentialSAT.SqrtLog.MomentsNativeCostBridge.Model

def weightedEnvelope (B d W N : ℕ) : ℕ :=
  25*N*(2*W+2*(d*B)+2)+11*(d*B)+9*d+
    N*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*W+57)+
    N*(220*(N+1)*(W+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2)+50

def dictionaryByteEnvelope (B d W L : ℕ) : ℕ := L*(2*W+2*(d*B)+2)

def normalizationEnvelope (B d W L : ℕ) : ℕ :=
  L*(220*(2*L+1)*(W+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2)+1

def productEnvelope (B d n u J L : ℕ) : ℕ :=
  L*(MomentsProgram.Product.stepEnvelope B d n u J (L*L) L+2)+1

def finishHeadEnvelope (B d n u J L H : ℕ) : ℕ :=
  14*dictionaryByteEnvelope B d (n+u+J) L+4*H+productEnvelope B d n u J L+23

def finishSupportEnvelope (B d n u J L : ℕ) : ℕ :=
  let E := dictionaryByteEnvelope B d (n+u+J) L
  200*(E+1)*(n+2)+14*n+27*E+9*d+normalizationEnvelope B d (n+u+J) L+60

def assignmentEnvelope (B d W L H A : ℕ) : ℕ :=
  9*H+A+weightedEnvelope B d W (2*L)+2*dictionaryByteEnvelope B d W L+10

def headEnvelope (B d n u J L H X A : ℕ) : ℕ :=
  36*H+30+X*(assignmentEnvelope B d (n+u+J) L H A+2)+
    finishHeadEnvelope B d n u J L H

def supportEnvelope (B d n u J L H X Y A : ℕ) : ℕ :=
  9*n+7*dictionaryByteEnvelope B d (n+u+J) L+7*H+19+
    Y*(headEnvelope B d n u J L H X A+2)+finishSupportEnvelope B d n u J L

def bucketEnvelope (B d n u J L H X Y S A : ℕ) : ℕ :=
  38*H+34+S*(supportEnvelope B d n u J L H X Y A+2)

def work (B d n u J L H X Y S A K : ℕ) : ℕ :=
  K*(bucketEnvelope B d n u J L H X Y S A+2)+2+
    MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) L+1

/-- A deliberately generous fixed polynomial. H includes serialized head and
bucket payload sizes; it is not assumed to be polynomial in the variable
count. X, S and K retain assignment, support and attained-label enumeration. -/
theorem work_le (B d n u J L H X Y S A K Z : ℕ)
    (hZ : 1 ≤ Z) (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z)
    (hJ : J ≤ Z) (hL : L ≤ Z) (hH : H ≤ Z) (hX : X ≤ Z) (hY : Y ≤ Z)
    (hS : S ≤ Z) (hA : A ≤ Z) (hK : K ≤ Z) :
    work B d n u J L H X Y S A K ≤ 4000000*Z^10 := by
  have hm : work B d n u J L H X Y S A K ≤ work Z Z Z Z Z Z Z Z Z Z Z Z := by
    unfold work bucketEnvelope supportEnvelope headEnvelope assignmentEnvelope
      finishHeadEnvelope finishSupportEnvelope productEnvelope normalizationEnvelope
      dictionaryByteEnvelope weightedEnvelope MomentsProgram.Product.stepEnvelope
      MomentsReadoutProgram.uniformReadoutBudget
      MomentsReadoutProgram.uniformSlotBudget MomentsProgram.Dictionary.codeBranchBudget
    dsimp only
    gcongr
  have he : work Z Z Z Z Z Z Z Z Z Z Z Z = topPolynomial Z := by
    unfold work bucketEnvelope supportEnvelope headEnvelope assignmentEnvelope
      finishHeadEnvelope finishSupportEnvelope productEnvelope normalizationEnvelope
      dictionaryByteEnvelope weightedEnvelope MomentsProgram.Product.stepEnvelope
      MomentsReadoutProgram.uniformReadoutBudget
      MomentsReadoutProgram.uniformSlotBudget MomentsProgram.Dictionary.codeBranchBudget topPolynomial
    ring
  rw [he] at hm
  exact hm.trans (topPolynomial_le Z hZ)

/-- Substitution into61's fixed-polynomial closure. The exponent a charges
ordinary bit dimensions; b may also charge enumeration and sparse capacity.
The cap hypothesis is numerical and must be discharged from actual fields,
not from a claimed running-time oracle. -/
theorem work_le_nativeEnvelope (B d n u J L H X Y S A K Z k N a b : ℕ)
    (p : CostAssembly.Resources) (hZ : 1 ≤ Z)
    (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z) (hJ : J ≤ Z) (hL : L ≤ Z)
    (hH : H ≤ Z) (hX : X ≤ Z) (hY : Y ≤ Z) (hS : S ≤ Z) (hA : A ≤ Z) (hK : K ≤ Z)
    (hcap : Z ≤ (N+1)^a*(CostAssembly.assembledWork k N p+1)^b) :
    work B d n u J L H X Y S A K ≤
      4000000*CostAssembly.nativeEnvelope k N (b*10) (a*10) p := by
  exact (work_le B d n u J L H X Y S A K Z hZ
    hB hd hn hu hJ hL hH hX hY hS hA hK).trans (power_substitution Z k N a b p hcap)

/-- Fully explicit capacity/enumeration substitution. The payload hypothesis
allows one whole serialized enumeration, rather than mistaking that length
for an ordinary parameter. The only producer premise is its separately
proved polynomial bound A; it does not stand in for the moment execution.
The exponents a and b are fixed when applying the uniform asymptotic theorem. -/
theorem work_le_resourceEnvelope
    (B d n u J L H X Y S A K k N a b : ℕ) (p : CostAssembly.Resources)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits)
    (hB : B ≤ (N+1)^a) (hd : d ≤ (N+1)^a) (hn : n ≤ (N+1)^a)
    (hu : u ≤ (N+1)^a) (hJ : J ≤ (N+1)^a)
    (hcapacity : L ≤ u*J*SupportProgram.count N (CostAssembly.jetOrder k N p))
    (hH : H ≤ (N+1)^a*
      (CostAssembly.enumerationWork p.labelBase p.labelRows p.heads p.headSize+1)*
      (SupportProgram.count N (CostAssembly.jetOrder k N p)+1))
    (hX : X ≤ CostAssembly.enumerationWork p.labelBase p.labelRows p.heads p.headSize)
    (hY : Y ≤ CostAssembly.enumerationWork p.labelBase p.labelRows p.heads p.headSize)
    (hS : S ≤ SupportProgram.count N (CostAssembly.jetOrder k N p))
    (hK : K ≤ CostAssembly.enumerationWork p.labelBase p.labelRows p.heads p.headSize)
    (hA : A ≤ (N+1)^a*(CostAssembly.assembledWork k N p+1)^b) :
    work B d n u J L H X Y S A K ≤
      4000000*CostAssembly.nativeEnvelope k N ((b+2)*10) ((a*2)*10) p := by
  let Z := (N+1)^(a*2)*(CostAssembly.assembledWork k N p+1)^(b+2)
  obtain ⟨hZ,hBZ,hdZ,hnZ,huZ,hJZ,hLZ,hHZ,hXZ,hYZ,hSZ,hAZ,hKZ⟩ :=
    resourceCaps B d n u J L H X Y S A K k N a b p
      hbase hheads hbits hB hd hn hu hJ hcapacity hH hX hY hS hK hA
  exact work_le_nativeEnvelope B d n u J L H X Y S A K Z k N (a*2) (b+2) p
    hZ hBZ hdZ hnZ huZ hJZ hLZ hHZ hXZ hYZ hSZ hAZ hKZ le_rfl

end SubexponentialSAT.SqrtLog.MomentsNativeCostBridge.Model

end OAI.Algorithms
