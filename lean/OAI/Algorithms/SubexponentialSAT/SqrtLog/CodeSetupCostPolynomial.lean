import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCostScale

namespace OAI.Algorithms

/-! Positive arithmetic normal forms for the exhaustive-search budgets.
The native-budget identities are established separately against25's actual
definitions. Here no machine execution is postulated. -/
namespace SubexponentialSAT.SqrtLog.CodeSetupCost

def generation (alphabet width depth count : ℕ) : ℕ :=
  100*(alphabet+depth+800*(depth+1)*(count+1)*((depth+1)*(2*width+1)+1)+10)

def matrix2 (entries rows : ℕ) : ℕ := 108123*entries+86*rows+6

def localWord (entries rows cols : ℕ) : ℕ :=
  matrix2 entries rows+10*rows+14*cols+18

def localCallback (entries rows cols distance : ℕ) : ℕ :=
  (35*entries+7*rows+7*distance+15*cols+25)+localWord entries rows cols+1+
    18*(2*((5*entries+5*cols+rows+distance+5)+localWord entries rows cols)+3)

def localVerifier (entries rows cols distance words : ℕ) : ℕ :=
  4+words*(30*cols+localCallback entries rows cols distance+7)

def localCandidate (entries rows cols distance words : ℕ) : ℕ :=
  25*entries+9*((10*cols+2)*words+1)+15+
    3*localVerifier entries rows cols distance words

def localNumeric (alphabet width rows cols distance entries words matrices : ℕ) : ℕ :=
  generation alphabet width cols words+generation alphabet width entries matrices+
    (4+matrices*(30*entries+localCandidate entries rows cols distance words+9))+2

def graphWord (entries rows cols qlen Dlen : ℕ) : ℕ :=
  (matrix2 entries rows+10*rows+10*cols+9)+700*(2*(qlen+Dlen+rows)+4)^2+5

def graphCallback (entries rows cols qlen Dlen : ℕ) : ℕ :=
  (35*entries+7*rows+7*qlen+7*Dlen+15*cols+31)+graphWord entries rows cols qlen Dlen+
    29*(2*((5*entries+5*cols+rows+qlen+Dlen+5)+graphWord entries rows cols qlen Dlen)+3)

def graphVerifier (entries rows cols qlen Dlen chars : ℕ) : ℕ :=
  4+chars*(30*cols+graphCallback entries rows cols qlen Dlen+7)

def graphCandidate (entries rows cols qlen Dlen chars : ℕ) : ℕ :=
  25*entries+9*((10*cols+2)*chars+1)+15+
    3*graphVerifier entries rows cols qlen Dlen chars

def graphNumeric (alphabet width rows cols qlen Dlen entries chars tuples : ℕ) : ℕ :=
  generation alphabet width cols chars+generation alphabet width entries tuples+
    (4+tuples*(30*entries+graphCandidate entries rows cols qlen Dlen chars+9))+2

theorem localNumeric_bound (a w t D d U P Q Z : ℕ)
    (ha : a ≤ Z) (hw : w ≤ Z) (ht : t ≤ Z) (hD : D ≤ Z) (hd : d ≤ Z)
    (hU : U ≤ Z) (hP : P ≤ Z) (hQ : Q ≤ Z) :
    localNumeric a w t D d U P Q ≤ 1000000000000*(Z+1)^6 := by
  calc
    _ ≤ localNumeric Z Z Z Z Z Z Z Z := by
      unfold localNumeric generation localCandidate localVerifier localCallback localWord matrix2
      gcongr
    _ ≤ _ := by
      unfold localNumeric generation localCandidate localVerifier localCallback localWord matrix2
      ring_nf
      omega

theorem graphNumeric_bound (a w D r ql Dl U P Q Z : ℕ)
    (ha : a ≤ Z) (hw : w ≤ Z) (hD : D ≤ Z) (hr : r ≤ Z) (hq : ql ≤ Z) (hd : Dl ≤ Z)
    (hU : U ≤ Z) (hP : P ≤ Z) (hQ : Q ≤ Z) :
    graphNumeric a w D r ql Dl U P Q ≤ 1000000000000*(Z+1)^6 := by
  calc
    _ ≤ graphNumeric Z Z Z Z Z Z Z Z Z := by
      unfold graphNumeric generation graphCandidate graphVerifier graphCallback graphWord matrix2
      gcongr
    _ ≤ _ := by
      unfold graphNumeric generation graphCandidate graphVerifier graphCallback graphWord matrix2
      ring_nf
      omega

/-- The constants and polynomial in encoded lengths are included explicitly.
The two count arguments are the actual numbers of tested candidates. -/
theorem combinedNumeric_bound (a₂ a₃ w₂ w₃ t D d r ql Dl f g H W C : ℕ)
    (ht : t ≤ H) (hD : D ≤ H) (hd : d ≤ H) (hr : r ≤ H)
    (hq : ql ≤ W) (hDl : Dl ≤ W)
    (hC : 1000000000000*(f+g+1)+a₂+a₃+w₂+w₃ ≤ C) :
    f*localNumeric a₃ w₃ t D d (t*D) (3^D) (3^(t*D))+
      g*graphNumeric a₂ w₂ D r ql Dl (D*r) (2^r) (2^(D*r))+1 ≤ envelope C H W := by
  have ha₂ : a₂ ≤ C := by omega
  have ha₃ : a₃ ≤ C := by omega
  have hw₂ : w₂ ≤ C := by omega
  have hw₃ : w₃ ≤ C := by omega
  have hc : 1000000000000*(f+g)+1 ≤ C := by omega
  let E := C+(H+1)^2
  let Y := 3^E
  let Z := Y*(W+1)
  have hE : H ≤ E := by dsimp [E]; nlinarith
  have hE2 : H*H ≤ E := by dsimp [E]; nlinarith
  have hCE : C ≤ E := by dsimp [E]; omega
  have hCY : C ≤ Y := hCE.trans (self_le_three_pow E)
  have hHY : H ≤ Y := hE.trans (self_le_three_pow E)
  have hYY : 1 ≤ Y := Nat.one_le_pow _ _ (by decide)
  have hYZ : Y ≤ Z := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left Y (Nat.succ_pos W)
  have hWZ : W ≤ Z := (Nat.le_succ W).trans (by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (W+1) hYY)
  have hUZ : t*D ≤ Z := (Nat.mul_le_mul ht hD).trans (hE2.trans ((self_le_three_pow E).trans hYZ))
  have hVZ : D*r ≤ Z := (Nat.mul_le_mul hD hr).trans (hE2.trans ((self_le_three_pow E).trans hYZ))
  have hp : 3^D ≤ Z := (Nat.pow_le_pow_right (by decide) (hD.trans hE)).trans hYZ
  have hq' : 3^(t*D) ≤ Z := (Nat.pow_le_pow_right (by decide)
    ((Nat.mul_le_mul ht hD).trans hE2)).trans hYZ
  have hp' : 2^r ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 3) r).trans
    ((Nat.pow_le_pow_right (by decide) (hr.trans hE)).trans hYZ)
  have hq'' : 2^(D*r) ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (D*r)).trans
    ((Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul hD hr).trans hE2)).trans hYZ)
  have hl := localNumeric_bound a₃ w₃ t D d (t*D) (3^D) (3^(t*D)) Z
    (ha₃.trans (hCY.trans hYZ)) (hw₃.trans (hCY.trans hYZ)) (ht.trans (hHY.trans hYZ)) (hD.trans (hHY.trans hYZ))
    (hd.trans (hHY.trans hYZ)) hUZ hp hq'
  have hg := graphNumeric_bound a₂ w₂ D r ql Dl (D*r) (2^r) (2^(D*r)) Z
    (ha₂.trans (hCY.trans hYZ)) (hw₂.trans (hCY.trans hYZ)) (hD.trans (hHY.trans hYZ)) (hr.trans (hHY.trans hYZ))
    (hq.trans hWZ) (hDl.trans hWZ) hVZ hp' hq''
  have hZ : 1 ≤ (Z+1)^6 := Nat.one_le_pow _ _ (Nat.succ_pos Z)
  have hcoeff : 1000000000000*(f+g)+1 ≤ Y := hc.trans hCY
  have hsum : f*localNumeric a₃ w₃ t D d (t*D) (3^D) (3^(t*D))+
      g*graphNumeric a₂ w₂ D r ql Dl (D*r) (2^r) (2^(D*r))+1 ≤ Y*(Z+1)^6 := by
    calc
      _ ≤ f*(1000000000000*(Z+1)^6)+g*(1000000000000*(Z+1)^6)+(Z+1)^6 :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left f hl)
          (Nat.mul_le_mul_left g hg)) hZ
      _ = (1000000000000*(f+g)+1)*(Z+1)^6 := by ring
      _ ≤ _ := Nat.mul_le_mul_right ((Z+1)^6) hcoeff
  have hz1 : 1 ≤ Z := hYY.trans hYZ
  have hz2 : Z+1 ≤ 3*Z := (Nat.add_le_add_left hz1 Z).trans (by
    simpa only [two_mul] using Nat.mul_le_mul_right Z (by decide : 2 ≤ 3))
  have hz : Z+1 ≤ 3*Y*(W+1) := by
    simpa only [Z,Nat.mul_assoc] using hz2
  calc
    _ ≤ Y*(Z+1)^6 := hsum
    _ ≤ Y*(3*Y*(W+1))^6 := by gcongr
    _ = 3^6*(3^E)^7*(W+1)^6 := by dsimp [Y]; ring
    _ = envelope C H W := by
      rw [← pow_mul,← pow_add]
      unfold envelope exponent E
      congr 2
      ring

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
