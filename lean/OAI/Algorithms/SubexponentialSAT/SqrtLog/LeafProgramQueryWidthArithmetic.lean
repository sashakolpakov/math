import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyRingSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramCost

namespace OAI.Algorithms

/-! A fixed ordinary polynomial bounds the literal ring, interpolation and
layout-denominator setup budgets, including their staging copies. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT LeafParametersProgram SubexpLiftRing CostAssembly.Polynomial

def interpolationEnvelope (S : ℕ) : ℕ :=
  1000*(S+1)^2*(16*(S+1)^2+S+1)*
    (100000*(S+1)^3*(2*S+1)^2+2*S*S+1)

theorem interpolation_bound (t d Q S : ℕ) (ht : t ≤ S) (hd : d ≤ S) (hQ : Q ≤ S)
    (hf : 3^d ≤ 16*(Q+1)^2) :
    InterpolationCacheProgram.budget t d Q ≤ interpolationEnvelope S := by
  have hi := InterpolationCacheProgram.budget_polynomial t d Q
  have hm := HornerProgram.Services.mulBudget_polynomial (baseWidth 3 t) d
  have ha := HornerProgram.Services.addBudget_polynomial (baseWidth 3 t) d
  simp only [RingProgram.ternary_baseWidth] at hm ha hi
  have hb : HornerProgram.Services.mulBudget (2*t) d+
      HornerProgram.Services.addBudget (2*t) d+d*(2*t)+1 ≤
      100000*(S+1)^3*(2*S+1)^2+2*S*S+1 := by
    have hm' : HornerProgram.Services.mulBudget (2*t) d ≤ 50000*(S+1)^3*(2*S+1)^2 :=
      hm.trans (by gcongr)
    have ha' : HornerProgram.Services.addBudget (2*t) d ≤ 50000*(S+1)^3*(2*S+1)^2 :=
      ha.trans (by gcongr)
    have hdt : d*(2*t) ≤ 2*S*S := by nlinarith [Nat.mul_le_mul hd ht]
    nlinarith only [hm',ha',hdt]
  unfold interpolationEnvelope
  exact (Nat.le_of_succ_le hi).trans (by gcongr; exact hf.trans (by gcongr))

def ringEnvelope (C e S : ℕ) : ℕ :=
  C*(S+1)^e+1+10000*(S+(C*(S+1)^e+1)+1+interpolationEnvelope S+2)
def arithmeticEnvelope (C e S : ℕ) : ℕ :=
  ringEnvelope C e S + LayoutDenominatorProgram.polynomialBudget S (2*S) S +
    600*(S+ringEnvelope C e S+3)

theorem interpolationEnvelope_ordinary : Ordinary interpolationEnvelope := by
  refine ⟨7000000000,9,?_⟩
  intro S
  let T := S+1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hS : S ≤ T := by dsimp [T]; omega
  have hS2 : 2*S+1 ≤ 2*T := by dsimp [T]; omega
  have ht2 : T ≤ T^2 := by simpa using Nat.pow_le_pow_right hT (show 1 ≤ 2 by decide)
  have ht0 : 1 ≤ T^5 := Nat.one_le_pow _ _ hT
  have ht25 : T^2 ≤ T^5 := Nat.pow_le_pow_right hT (by decide)
  have hleft : 16*(S+1)^2+S+1 ≤ 17*T^2 := by dsimp [T] at *; nlinarith
  have hright : 100000*(S+1)^3*(2*S+1)^2+2*S*S+1 ≤ 400003*T^5 := by
    have hmain : 100000*(S+1)^3*(2*S+1)^2 ≤ 400000*T^5 := by
      calc
        _ ≤ 100000*T^3*(2*T)^2 := by dsimp [T]; gcongr
        _ = _ := by ring
    have hsquare : 2*S*S ≤ 2*T^2 := by nlinarith
    nlinarith only [hmain,hsquare,ht25,ht0]
  unfold interpolationEnvelope
  calc
    _ ≤ 1000*T^2*(17*T^2)*(400003*T^5) := by gcongr
    _ ≤ 7000000000*(S+1)^9 := by dsimp [T]; nlinarith [Nat.zero_le ((S+1)^9)]

theorem denominatorEnvelope_ordinary :
    Ordinary (fun S=>LayoutDenominatorProgram.polynomialBudget S (2*S) S) := by
  have h := ordinary_id
  have hb := ordinary_mul (ordinary_const 2) h
  have hp := ordinary_mul (ordinary_pow (ordinary_add h (ordinary_const 1)) 3)
    (ordinary_pow (ordinary_add hb (ordinary_const 1)) 2)
  have hprod := ordinary_mul h hb
  have hfirst := ordinary_mul hb (ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 100000) hp) (ordinary_mul (ordinary_const 80) hprod)) (ordinary_const 110))
  have hsecond := ordinary_add (ordinary_add (ordinary_mul (ordinary_const 200000) hp)
    (ordinary_mul (ordinary_const 203) hprod)) (ordinary_const 251)
  have hthird := ordinary_mul h (ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 50000) hp) (ordinary_mul (ordinary_const 8) hprod)) (ordinary_const 11))
  have result := ordinary_add (ordinary_add (ordinary_add (ordinary_add
    (ordinary_add hfirst hsecond) hthird) (ordinary_mul (ordinary_const 7) h))
    (ordinary_mul (ordinary_const 27) hprod)) (ordinary_const 32)
  simpa only [LayoutDenominatorProgram.polynomialBudget,Nat.add_assoc,Nat.mul_assoc] using result

theorem arithmeticEnvelope_ordinary (C e : ℕ) : Ordinary (arithmeticEnvelope C e) := by
  have hp := ordinary_add (ordinary_mul (ordinary_const C)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) e)) (ordinary_const 1)
  have hr : Ordinary (ringEnvelope C e) := by
    unfold ringEnvelope
    exact ordinary_add hp (ordinary_mul (ordinary_const 10000)
      (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id hp)
        (ordinary_const 1)) interpolationEnvelope_ordinary) (ordinary_const 2)))
  unfold arithmeticEnvelope
  exact ordinary_add (ordinary_add hr denominatorEnvelope_ordinary)
    (ordinary_mul (ordinary_const 600) (ordinary_add (ordinary_add ordinary_id hr) (ordinary_const 3)))

theorem arithmetic_budget_polynomial : ∃ C e : ℕ, ∀ (m : Circuit.Model) (W V L R S : ℕ),
    W ≤ S → V ≤ S → L ≤ S → R ≤ S → (∀i,m.len i ≤ S) → (∀i,m.val i ≤ S) →
    3^(m.val 34) ≤ 16*(m.val 21+1)^2 → arithmeticBudget m W V L R ≤ C*(S+1)^e := by
  obtain ⟨C,e,hp⟩ := CostAssembly.RingSetup.producerBudget_ordinary
  obtain ⟨A,d,had⟩ := arithmeticEnvelope_ordinary C e
  refine ⟨A,d,?_⟩
  intro m W V L R S hW hV hL hR hl hv hf
  have hprod := hp m W V L S hW hV hL hl (hv 33) (hv 34) (hv 21) hf
  have hi := interpolation_bound (m.val 33) (m.val 34) (m.val 21) S (hv 33) (hv 34) (hv 21) hf
  have hr : Ring.budget m W V L ≤ ringEnvelope C e S := by
    dsimp only [Ring.budget,ringEnvelope]
    omega
  have hd := LayoutDenominatorProgramQuery.budget_polynomial R (m.val 33) (m.val 34)
    (W+Ring.budget m W V L+1)
  simp only [RingProgram.ternary_baseWidth] at hd
  have hpoly : LayoutDenominatorProgram.polynomialBudget R (2*m.val 33) (m.val 34) ≤
      LayoutDenominatorProgram.polynomialBudget S (2*S) S := by
    unfold LayoutDenominatorProgram.polynomialBudget
    gcongr <;> first | exact hv 33 | exact hv 34
  apply le_trans _ (had S)
  unfold arithmeticBudget arithmeticEnvelope
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
