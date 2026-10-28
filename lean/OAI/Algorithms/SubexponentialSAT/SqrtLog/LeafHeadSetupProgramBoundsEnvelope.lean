import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPayload
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsMatrix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyDomination

namespace OAI.Algorithms

/-! Closed bounds for every Cartesian prefix, and absorption of fixed native
head-loop polynomials. The product parameter counts attained buckets; the
independent head-size parameter pays for every assignment inside each bucket. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open BucketTupleProgram
open BucketTupleProgram.Representative (headsBits tuplesBits)
open CostAssembly

 theorem enumerate_prefix_resources (tables : List HeadTable) (j r L K : ℕ)
    (hr : tables.length ≤ r)
    (ht : ∀ table∈tables,∀ h∈table.choices,(SubexponentialSAT.Encoding.frame h.bits).length ≤ L)
    (hne : ∀ table∈tables,1 ≤ table.buckets.length)
    (hK : (tables.map fun h=>h.buckets.length).prod ≤ K) :
    (enumerate (tables.take j)).length ≤ K ∧
    (∀ row∈enumerate (tables.take j),(headsBits row).length ≤ r*L) ∧
    (tuplesBits (enumerate (tables.take j))).length ≤ 1+(2*(r*L)+2)*K := by
  have hj : (tables.take j).length ≤ r := by
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans hr
  have ht' : ∀ table∈tables.take j,∀ h∈table.choices,(SubexponentialSAT.Encoding.frame h.bits).length ≤ L :=
    fun table hm => ht table (List.mem_of_mem_take hm)
  have hprod := (prefix_product_le tables j hne).trans hK
  refine ⟨?_,?_,?_⟩
  · simpa only [enumerate_length] using hprod
  · have hw := enumerateFrom_width (tables.take j) [[]] 0 L (by simp [headsBits]) ht'
    intro row hm
    exact (hw row hm).trans (by simpa using Nat.mul_le_mul_right L hj)
  · exact (enumerate_bytes (tables.take j) L ht').trans (by gcongr)

 theorem matrixEnvelope_le_nativeEnvelope {qi ql d k n : ℕ} {p : Resources}
    (hp : CostAssembly.Bounds qi ql d n p) (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (W : List Bool) (T B D free h : ℕ)
    (hh : h ≤ p.headSize) (hs : matrixSize W T B D free h ≤ p.ordinary+1) :
    matrixEnvelope W T B D free h ≤ 200000000*nativeEnvelope k n 2 (d*6) p := by
  have he := quadratic_headAssignments_le k n p hp.base hheads hbits
  have ho := ordinary_power_le hp hbits 6
  have hhpow : (2:ℕ)^h ≤ 2^p.headSize := Nat.pow_le_pow_right (by decide) hh
  have hpow : (2^h+1)^2 ≤ (assembledWork k n p+1)^2 :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right hhpow 1) 2).trans he
  unfold matrixEnvelope nativeEnvelope
  calc
    _ ≤ 200000000*(assembledWork k n p+1)^2*(p.ordinary+1)^6 := by gcongr
    _ ≤ 200000000*(assembledWork k n p+1)^2*(n+1)^(d*6) := by gcongr
    _ = _ := by ring

 theorem polynomial_loop_nativeEnvelope {qi ql d k n : ℕ} {p : Resources}
    (hp : CostAssembly.Bounds qi ql d n p) (hbits : 1 ≤ p.bits)
    (r Z C a b : ℕ) (hr : r ≤ p.ordinary+1)
    (hZ : Z ≤ C*(p.ordinary+1)^a*(assembledWork k n p+1)^b) :
    r*(100000000*(Z+1)^4)+2*r+2 ≤
      (100000000*(C+1)^4+4)*nativeEnvelope k n (4*b) (d*(4*a+1)) p := by
  let O := p.ordinary+1
  let V := assembledWork k n p+1
  have hO : 1 ≤ O := by dsimp [O]; omega
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hOa : 1 ≤ O^a := one_le_pow₀ hO
  have hVb : 1 ≤ V^b := one_le_pow₀ hV
  have hX : 1 ≤ O^a*V^b := by nlinarith only [hOa,hVb]
  have hZ' : Z+1 ≤ (C+1)*O^a*V^b := by
    change Z ≤ C*O^a*V^b at hZ
    nlinarith only [hZ,hX]
  have hp4 : (Z+1)^4 ≤ (C+1)^4*O^(4*a)*V^(4*b) := by
    calc
      _ ≤ ((C+1)*O^a*V^b)^4 := Nat.pow_le_pow_left hZ' 4
      _ = _ := by simp only [mul_pow,←pow_mul]; congr 2 <;> ring
  have htail : O ≤ O^(4*a+1)*V^(4*b) := by
    have ho : O ≤ O^(4*a+1) := le_self_pow₀ hO (by omega)
    have hv : 1 ≤ V^(4*b) := one_le_pow₀ hV
    nlinarith only [ho,hv]
  have hone : 1 ≤ O^(4*a+1)*V^(4*b) := hO.trans htail
  have hmain : r*(100000000*(Z+1)^4) ≤
      100000000*(C+1)^4*(O^(4*a+1)*V^(4*b)) := by
    calc
      _ ≤ O*(100000000*((C+1)^4*O^(4*a)*V^(4*b))) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hall : r*(100000000*(Z+1)^4)+2*r+2 ≤
      (100000000*(C+1)^4+4)*(O^(4*a+1)*V^(4*b)) := by
    change r ≤ O at hr
    nlinarith only [hmain,hr,htail,hone]
  have ho := ordinary_power_le hp hbits (4*a+1)
  unfold nativeEnvelope
  exact hall.trans (by dsimp [O,V] at *; gcongr)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
