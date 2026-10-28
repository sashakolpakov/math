import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostPadding

namespace OAI.Algorithms

/-! Substitution of a concrete node-time polynomial and the actual setup-width
polynomial into the complete query envelope. Constants precede every input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT

 theorem monomial_mono_exponents (x y z a b c A B C : ℕ)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    (x+1)^a*(y+1)^b*(z+1)^c ≤ (x+1)^A*(y+1)^B*(z+1)^C := by
  exact Nat.mul_le_mul (Nat.mul_le_mul
    (Nat.pow_le_pow_right (by omega) ha) (Nat.pow_le_pow_right (by omega) hb))
    (Nat.pow_le_pow_right (by omega) hc)

 theorem queryCap_from_node_padding (CI dI CU dU CK a b c : ℕ) :
    ∃ C e : ℕ, ∀ (input V work I U K N : ℕ),
    I ≤ CI*(input+1)^dI*(V+1)^dI →
    U ≤ CU*(input+1)^dU*(V+1)^dU →
    K ≤ CK*(I+1)^a*(V+1)^b*(work+1)^c → N ≤ work →
    queryCap U K N ≤ C*(input+1)^e*(V+1)^e*(work+1)^e := by
  obtain ⟨CQ,eQ,hQ⟩ := queryCap_padding
  let E := dU+dI*a+b+c+1
  let D := CU+CK*(CI+1)^a+1
  refine ⟨CQ*(D+1)^eQ,E*eQ,?_⟩
  intro input V work I U K N hI hU hK hN
  have hp : 1 ≤ (input+1)^dI*(V+1)^dI := by
    have hx : 1 ≤ (input+1)^dI := Nat.one_le_pow _ _ (by omega)
    have hy : 1 ≤ (V+1)^dI := Nat.one_le_pow _ _ (by omega)
    simpa only [one_mul] using Nat.mul_le_mul hx hy
  have hI1 : I+1 ≤ (CI+1)*(input+1)^dI*(V+1)^dI := by nlinarith only [hI,hp]
  have hK' : K ≤ (CK*(CI+1)^a)*(input+1)^(dI*a)*(V+1)^(dI*a+b)*(work+1)^c := by
    calc
      _ ≤ CK*((CI+1)*(input+1)^dI*(V+1)^dI)^a*(V+1)^b*(work+1)^c := hK.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hI1 a))))
      _ = _ := by simp only [mul_pow,←pow_mul, pow_add]; ring
  have HU : U ≤ D*(input+1)^E*(V+1)^E*(work+1)^E := by
    calc
      _ ≤ CU*(input+1)^dU*(V+1)^dU := hU
      _ = CU*((input+1)^dU*(V+1)^dU*(work+1)^0) := by simp; ring
      _ ≤ D*((input+1)^E*(V+1)^E*(work+1)^E) := Nat.mul_le_mul (by dsimp [D]; omega)
        (monomial_mono_exponents input V work dU dU 0 E E E (by dsimp [E]; omega)
          (by dsimp [E]; omega) (by omega))
      _ = _ := by ring
  have HK : K ≤ D*(input+1)^E*(V+1)^E*(work+1)^E := by
    calc
      _ ≤ (CK*(CI+1)^a)*((input+1)^(dI*a)*(V+1)^(dI*a+b)*(work+1)^c) := by simpa only [Nat.mul_assoc] using hK'
      _ ≤ D*((input+1)^E*(V+1)^E*(work+1)^E) := Nat.mul_le_mul (by dsimp [D]; omega)
        (monomial_mono_exponents input V work (dI*a) (dI*a+b) c E E E
          (by dsimp [E]; omega) (by dsimp [E]; omega) (by dsimp [E]; omega))
      _ = _ := by ring
  have HN : N ≤ D*(input+1)^E*(V+1)^E*(work+1)^E := by
    have hbase := monomial_mono_exponents input V work 0 0 1 E E E
      (by omega) (by omega) (by dsimp [E]; omega)
    simp only [pow_zero,one_mul,pow_one] at hbase
    have hD : 1 ≤ D := by dsimp [D]; omega
    have hmul := Nat.mul_le_mul_right ((input+1)^E*(V+1)^E*(work+1)^E) hD
    simp only [one_mul] at hmul
    exact hN.trans ((Nat.le_succ work).trans (hbase.trans (by simpa only [Nat.mul_assoc] using hmul)))
  simpa only [Nat.mul_assoc] using hQ U K N input V work D E E E HU HK HN

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
