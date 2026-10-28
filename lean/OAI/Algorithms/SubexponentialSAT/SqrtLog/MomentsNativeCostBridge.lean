import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramUniformBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsNativeCostModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramGrowth
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSupportCount

namespace OAI.Algorithms

/-! Explicit numerical substitution for the native moment stages. This file
uses the assembly's proved envelopes, rather than replacing primitive work by
an algebraic-operation counter. In particular all repeated projections,
normalizations, coefficient scalings and dictionary products remain charged. -/
namespace SubexponentialSAT.SqrtLog.MomentsNativeCostBridge
open MomentsAssembly

theorem dictionaryCapacity_eq_count {n : ℕ} (vars : Finset (Fin n)) (u J : ℕ) :
    dictionaryCapacity vars u J = u*J*SupportProgram.count vars.card J := by
  simp [dictionaryCapacity,Squarefree.Sparse.supportUniverse_card,SupportProgram.count]

theorem dictionaryCapacity_le_count {n : ℕ} (vars : Finset (Fin n)) (u J N : ℕ)
    (hvars : vars.card ≤ N) : dictionaryCapacity vars u J ≤ u*J*SupportProgram.count N J := by
  rw [dictionaryCapacity_eq_count]
  exact Nat.mul_le_mul_left _ (SupportProgram.count_mono_variables J hvars)

/-- Native bucket loop, scalar readout, and the final halt. The dictionary
capacity is L=u*J*M; callers substitute this equality after using the actual
validity/unique-key storage bound. -/
def work (B d n u J L H X Y S A K : ℕ) : ℕ :=
  K*(bucketEnvelope B d n u J L H X Y S A+2)+2+
    MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) L+1

theorem work_eq_model (B d n u J L H X Y S A K : ℕ) :
    work B d n u J L H X Y S A K = Model.work B d n u J L H X Y S A K := rfl

/-- Direct adapter for the bounds used by denseProgram_run. The two premises
are respectively bucketsWork_le and the final EntryInvariant storage bound. -/
theorem sum_le_work (B d n u J L H X Y S A K bucketTime entries : ℕ)
    (hb : bucketTime ≤ K*(bucketEnvelope B d n u J L H X Y S A+2)+2)
    (he : entries ≤ L) :
    bucketTime+MomentsReadoutProgram.uniformReadoutBudget B d n u J
      (n+u+J) entries+1 ≤ work B d n u J L H X Y S A K := by
  have hr : MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) entries ≤
      MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) L := by
    unfold MomentsReadoutProgram.uniformReadoutBudget MomentsReadoutProgram.uniformSlotBudget
    gcongr
  unfold work
  omega

/-- A deliberately generous fixed polynomial. H includes serialized head and
bucket payload sizes; it is not assumed to be polynomial in the variable
count. X, S and K retain assignment, support and attained-label enumeration. -/
theorem work_le (B d n u J L H X Y S A K Z : ℕ)
    (hZ : 1 ≤ Z) (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z)
    (hJ : J ≤ Z) (hL : L ≤ Z) (hH : H ≤ Z) (hX : X ≤ Z) (hY : Y ≤ Z)
    (hS : S ≤ Z) (hA : A ≤ Z) (hK : K ≤ Z) :
    work B d n u J L H X Y S A K ≤ 4000000*Z^10 := by
  change Model.work B d n u J L H X Y S A K ≤ _
  exact Model.work_le B d n u J L H X Y S A K Z hZ
    hB hd hn hu hJ hL hH hX hY hS hA hK

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

end SubexponentialSAT.SqrtLog.MomentsNativeCostBridge

end OAI.Algorithms
