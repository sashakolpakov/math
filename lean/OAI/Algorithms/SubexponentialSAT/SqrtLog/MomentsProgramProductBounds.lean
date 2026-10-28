import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProduct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramNormalize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeScaleProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem keptJoin_length {n B d : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) : (keptJoin a u J entries).length ≤ entries.length := by
  induction entries with
  | nil => simp [keptJoin]
  | cons b entries ih =>
    by_cases h : (a.join b.1).Kept u J <;> simp [keptJoin,h] <;> omega

theorem keptJoin_keyBound {n B d : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) (keptJoin a u J entries) := by
  induction entries with
  | nil => intro b hb; simp [keptJoin] at hb
  | cons b entries ih =>
    intro c hc
    by_cases h : (a.join b.1).Kept u J
    · simp only [keptJoin,h,ite_true,List.mem_cons] at hc
      rcases hc with rfl|hc
      · have hh := Squarefree.encodeIndex_length_le (a.join b.1) h
        change (Squarefree.encodeIndex (a.join b.1)).length ≤ n+u+J
        omega
      · exact ih c hc
    · simp only [keptJoin,h,ite_false] at hc
      exact ih c hc

theorem block_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    (block p t M cache table u J a right).length ≤ right.length := by
  simpa [block,Squarefree.ScaleProgram.scaled] using
    keptJoin_length a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)

theorem block_keyBound (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) (block p t M cache table u J a right) := by
  intro b hb
  apply keptJoin_keyBound a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right) b
  simpa [block] using hb

theorem bytes_length_le {n B d : ℕ} (entries : List (Entry n B d)) (W : ℕ)
    (h : Normalize.KeyBound Squarefree.encodeIndex W entries) :
    (bytes entries).length ≤ entries.length*(2*W+2*(d*B)+2) := by
  have hh := Dictionary.rawEntries_length_le
    (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) W (d*B)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact h b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2))
  simpa [bytes,Normalize.bytes,Squarefree.Program.encodeDictionary] using hh

theorem normalize_keyBound (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {K : Type*} [DecidableEq K] {d : ℕ}
    (key : K → List Bool) (W : ℕ)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : Normalize.KeyBound key W source) (hi : Normalize.KeyBound key W seed) :
    Normalize.KeyBound key W (Normalize.run p t M cache source seed) := by
  induction source generalizing seed with
  | nil => exact hi
  | cons a source ih =>
    apply ih _ (fun b hb => hs b (by simp [hb]))
    exact Normalize.insertCode_keyBound p t M cache key W seed a.1 a.2 (hs a (by simp)) hi

/-- Explicit polynomial envelope for one outer product iteration. -/
def stepEnvelope (B d n u J N r : ℕ) : ℕ :=
  let W := n+u+J
  let C := d*B
  11*W+20*C+9*u+9*J+9*d+100 + r *
    (25*(2*W+2*C+2) +
     (40000*(d+1)^3*(B+1)^2+35*C+7*d+22*W+57) +
     (100*(n+u+J+C+2)+2) +
     (220*(N+1)*(W+C+1)+Dictionary.codeBranchBudget B d+2))

theorem stepBudget_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J N : ℕ)
    (a : Entry n (baseWidth p t) d) (right seed : List (Entry n (baseWidth p t) d))
    (ha : a.1.Kept u J) (hr : ∀ b ∈ right, b.1.Kept u J)
    (hi : Normalize.KeyBound Squarefree.encodeIndex (n+u+J) seed)
    (hN : right.length+seed.length ≤ N) :
    stepBudget p t M cache table u J a right seed ≤
      stepEnvelope (baseWidth p t) d n u J N right.length := by
  let W := n+u+J
  let C := d*baseWidth p t
  let scaled := Squarefree.ScaleProgram.scaled p t M cache table a.2 right
  let source := block p t M cache table u J a right
  have hk : (Squarefree.encodeIndex a.1).length ≤ W := by
    have h := Squarefree.encodeIndex_length_le a.1 ha; dsimp [W]; omega
  have hright : Normalize.KeyBound Squarefree.encodeIndex W right := by
    intro b hb; have h := Squarefree.encodeIndex_length_le b.1 (hr b hb); dsimp [W]; omega
  have hscaled : Normalize.KeyBound Squarefree.encodeIndex W scaled := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact hright c hc
  have hsl : scaled.length = right.length := by simp [scaled,Squarefree.ScaleProgram.scaled]
  have hbl : source.length ≤ right.length := block_length p t M cache table u J a right
  have hbs : Normalize.KeyBound Squarefree.encodeIndex W source := block_keyBound p t M cache table u J a right
  have hbr := bytes_length_le right W hright
  have hbc := bytes_length_le scaled W hscaled
  have hbb := bytes_length_le source W hbs
  have hb := Squarefree.ScaleProgram.budget_le Squarefree.encodeIndex right W hright
  have hm := Squarefree.KeyMapProgram.budget_bound a.1 u J C (coefficientBytes scaled) ha
    (by intro b hb; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc; exact hr e he)
    (by intro b hb; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb; exact le_of_eq (RingProgram.flat_length c.2))
  have hn := Normalize.work_le p t M cache Squarefree.encodeIndex W N source seed hbs hi (by omega)
  have hnb := Nat.mul_le_mul_right
    (220*(N+1)*(W+C+1)+Dictionary.codeBranchBudget (baseWidth p t) d+2) hbl
  have hbb' := Nat.mul_le_mul_right (2*W+2*C+2) hbl
  simp only [coefficientBytes,List.length_map] at hm
  rw [hsl] at hbc hm
  unfold stepBudget stepEnvelope
  simp only [RingProgram.flat_length]
  dsimp [scaled,source,W,C] at *
  simp only [coefficientBytes]
  nlinarith only [hk,hbr,hbc,hbb,hb,hm,hn,hnb,hbb']

/-- Quadratic record accumulation is paid explicitly; no sparse lookup is free. -/
theorem work_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J N : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hl : ∀ a ∈ left, a.1.Kept u J) (hr : ∀ b ∈ right, b.1.Kept u J)
    (hi : Normalize.KeyBound Squarefree.encodeIndex (n+u+J) seed)
    (hN : left.length*right.length+seed.length ≤ N) :
    work p t M cache table u J left right seed ≤
      left.length*(stepEnvelope (baseWidth p t) d n u J N right.length+2)+1 := by
  induction left generalizing seed with
  | nil => simp [work]
  | cons a left ih =>
    let next := Normalize.run p t M cache (block p t M cache table u J a right) seed
    have hs := Normalize.run_length p t M cache (block p t M cache table u J a right) seed
    have hb := block_length p t M cache table u J a right
    have hn : left.length*right.length+next.length ≤ N := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hN
      dsimp [next]; omega
    have hnext := normalize_keyBound p t M cache Squarefree.encodeIndex (n+u+J)
      (block p t M cache table u J a right) seed (block_keyBound p t M cache table u J a right) hi
    have hrec := ih next (fun a ha => hl a (by simp [ha])) hnext hn
    have hstep := stepBudget_le p t M cache table u J N a right seed (hl a (by simp)) hr hi
      (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hN; omega)
    dsimp only [next] at hrec
    simp only [work,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
