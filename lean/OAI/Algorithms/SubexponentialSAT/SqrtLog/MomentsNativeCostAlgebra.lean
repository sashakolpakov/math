import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyDomination

namespace OAI.Algorithms

/-! Arithmetic for the explicit native-moment cost envelope, isolated from
machine refinement so it can be checked independently of the assembly. -/
namespace SubexponentialSAT.SqrtLog.MomentsNativeCostBridge

def topPolynomial (Z : ℕ) : ℕ :=
  120000*Z^10+600220*Z^9+1219540*Z^8+1240029*Z^7+628848*Z^6+
  143183*Z^5+23130*Z^4+8357*Z^3+954*Z^2+80*Z+27

theorem topPolynomial_le (Z : ℕ) (hZ : 1 ≤ Z) : topPolynomial Z ≤ 4000000*Z^10 := by
  have hp (j : ℕ) (hj : j ≤ 10) : Z^j ≤ Z^10 := Nat.pow_le_pow_right hZ hj
  have h0 : 1 ≤ Z^10 := by simpa using hp 0 (by decide)
  have h1 : Z ≤ Z^10 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  unfold topPolynomial
  omega

theorem power_substitution (Z k N a b : ℕ) (p : CostAssembly.Resources)
    (hcap : Z ≤ (N+1)^a*(CostAssembly.assembledWork k N p+1)^b) :
    4000000*Z^10 ≤
      4000000*CostAssembly.nativeEnvelope k N (b*10) (a*10) p := by
  calc
    _ ≤ 4000000*((N+1)^a*(CostAssembly.assembledWork k N p+1)^b)^10 := by gcongr
    _ = _ := by simp only [CostAssembly.nativeEnvelope,mul_pow,←pow_mul]

theorem resourceCaps
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
    let Z := (N+1)^(a*2)*(CostAssembly.assembledWork k N p+1)^(b+2)
    1 ≤ Z ∧ B ≤ Z ∧ d ≤ Z ∧ n ≤ Z ∧ u ≤ Z ∧ J ≤ Z ∧ L ≤ Z ∧ H ≤ Z ∧
      X ≤ Z ∧ Y ≤ Z ∧ S ≤ Z ∧ A ≤ Z ∧ K ≤ Z := by
  let D := (N+1)^a
  let W := CostAssembly.assembledWork k N p+1
  let Z := D^2*W^(b+2)
  have hD : 1 ≤ D := Nat.one_le_pow _ _ (by omega)
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hD2 : D ≤ D^2 := by
    simpa only [Nat.mul_one,pow_two] using Nat.mul_le_mul_left D hD
  have hDsq : 1 ≤ D^2 := hD.trans hD2
  have hWb : W^b ≤ W^(b+2) := Nat.pow_le_pow_right hW (by omega)
  have hW2 : W^2 ≤ W^(b+2) := Nat.pow_le_pow_right hW (by omega)
  have hW1 : W ≤ W^(b+2) := by
    simpa using Nat.pow_le_pow_right hW (show 1 ≤ b+2 by omega)
  have hWp : 1 ≤ W^(b+2) := Nat.one_le_pow _ _ hW
  have hZ : 1 ≤ Z := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hDsq hWp
  have hDZ : D ≤ Z := by
    exact hD2.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (D^2) hWp)
  have hWZ : W ≤ Z := by
    exact hW1.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (W^(b+2)) hDsq)
  have hE := CostAssembly.enumeration_le_assembledWork k N p hbits
  have hM := CostAssembly.supportCount_le_assembledWork k N p hbase hheads hbits
  have hEp : CostAssembly.enumerationWork p.labelBase p.labelRows p.heads p.headSize+1 ≤ W := by
    dsimp [W]; omega
  have hMp : SupportProgram.count N (CostAssembly.jetOrder k N p)+1 ≤ W := by
    dsimp [W]; omega
  have hL : L ≤ Z := by
    calc
      L ≤ u*J*SupportProgram.count N (CostAssembly.jetOrder k N p) := hcapacity
      _ ≤ D*D*W := by gcongr ; omega
      _ ≤ D^2*W^(b+2) := by rw [pow_two]; gcongr
  have hHZ : H ≤ Z := by
    calc
      H ≤ D*W*W := hH.trans (by dsimp only [D]; gcongr)
      _ ≤ D^2*W^2 := by
        simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul_right (W*W) hD2
      _ ≤ Z := by dsimp [Z]; gcongr
  have hAZ : A ≤ Z := by
    calc
      A ≤ D*W^b := hA
      _ ≤ D^2*W^(b+2) := by gcongr
  have hXZ : X ≤ Z := (hX.trans (le_trans (by omega :
      CostAssembly.enumerationWork p.labelBase p.labelRows p.heads p.headSize ≤ W) hWZ))
  have hYZ : Y ≤ Z := hY.trans (le_trans (by omega) hWZ)
  have hKZ : K ≤ Z := hK.trans (le_trans (by omega) hWZ)
  have hSZ : S ≤ Z := hS.trans (le_trans (by omega) hWZ)
  have hzdef : Z = (N+1)^(a*2)*(CostAssembly.assembledWork k N p+1)^(b+2) := by
    dsimp [Z,D,W]
    rw [pow_mul]
  rw [←hzdef]
  exact ⟨hZ,hB.trans hDZ,hd.trans hDZ,hn.trans hDZ,hu.trans hDZ,hJ.trans hDZ,
    hL,hHZ,hXZ,hYZ,hSZ,hAZ,hKZ⟩

end SubexponentialSAT.SqrtLog.MomentsNativeCostBridge

end OAI.Algorithms
