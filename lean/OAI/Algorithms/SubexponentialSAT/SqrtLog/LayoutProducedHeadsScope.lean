import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramModel

namespace OAI.Algorithms

/-! The native scope selector has precisely the rational weights required by
the correlated-packing proof. All lists here are the actual producer lists. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes PackingProgram
open PackingProgram.Assembly

theorem scope_terms_complete (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (Q : ℕ) : ∀ z,z ∈ Scope.terms scopes n mask Q := by
  intro z
  cases z with
  | inl p =>
    rcases p with ⟨i,j⟩
    simp [Scope.terms,Scope.pairs,PackingIncidenceInput.Finished.incidenceList]
  | inr p => rcases p with ⟨t,v,w⟩; simp [Scope.terms,PackingHeadIncremental.headTerms]

theorem scope_terms_nodup (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (Q : ℕ) : (Scope.terms scopes n mask Q).Nodup := by
  let vertices := List.finRange n
  let heads := (List.finRange Q).product (vertices.product vertices)
  have he : PackingHeadIncremental.headTerms
      (I := PackingIncidenceInput.Semantics.Incidences scopes mask) (Q := Q) vertices =
      heads.map (fun z => Sum.inr (z.1,z.2.1,z.2.2)) := by
    simp [PackingHeadIncremental.headTerms,heads,List.product,List.map_flatMap,
      List.map_map,Function.comp_def]
  have hh : heads.Nodup := (List.nodup_finRange Q).product
    ((List.nodup_finRange n).product (List.nodup_finRange n))
  have hi : Function.Injective (fun z : Fin Q × Fin n × Fin n =>
      (Sum.inr (z.1,z.2.1,z.2.2) : Packing.ScoreTerm
        (PackingIncidenceInput.Semantics.Incidences scopes mask) (Fin n) Q)) := by
    intro z w h; simpa using h
  unfold Scope.terms
  change ((Scope.pairs scopes mask).map Sum.inl ++
    PackingHeadIncremental.headTerms vertices).Nodup
  rw [he,List.nodup_append]
  refine ⟨?_,hh.map hi,?_⟩
  · exact ((List.nodup_finRange _).product (List.nodup_finRange _)).map Sum.inl_injective
  · intro x hx y hy hxy
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hy
    exact Sum.inl_ne_inr hxy

theorem complete_alphabet_length {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    (a::tail).length=r^Q := by
  have he : (a::tail).toFinset=Finset.univ :=
    Finset.eq_univ_of_forall (fun z => List.mem_toFinset.mpr (haC z))
  calc
    _ = (a::tail).toFinset.card := (List.toFinset_card_of_nodup haN).symm
    _ = r^Q := by rw [he]; simp

def problemX (p : PackingCallerProgram.Problem) : ℚ :=
  (1/(p.s:ℚ))*p.incidences/(Fintype.card (UniversalType p.r p.Q 1):ℚ)

def problemWeights (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Weights :=
  Scope.weights p.n p.s p.incidences p.r (a::tail).length p.hs p.hr (by simp)

def problemAssignment (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  Packing.computedWords
    (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
    (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
    a tail (Scope.terms p.scopes p.n p.mask p.Q)
    (PackingIncidenceInput.Semantics.seedIndices p.n p.factors)
    (problemX p) ((p.n:ℚ)/(2*(p.r:ℚ)))

theorem problem_x_eq (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    problemX p=(p.incidences:ℚ)/((p.s:ℚ)*(a::tail).length^2) := by
  unfold problemX
  rw [complete_alphabet_length a tail haN haC]
  simp only [card_universalType,Nat.cast_pow]
  rw [show p.Q*(1+1)=p.Q*2 by omega,pow_mul]
  ring

theorem problem_weight_head (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    (problemX p)^2=((problemWeights p a tail).head:ℚ)/(problemWeights p a tail).denominator := by
  rw [problem_x_eq p a tail haN haC]
  simpa only [problemWeights,Scope.weights,Nat.cast_mul,Nat.cast_pow] using
    Weights.ofFractions_head p.incidences (p.s*(a::tail).length^2) p.n (2*p.r)
      (Nat.mul_pos p.hs (pow_pos (by simp) 2)) (Nat.mul_pos (by decide) p.hr)

theorem problem_weight_incidence (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    ((p.n:ℚ)/(2*(p.r:ℚ)))^2=((problemWeights p a tail).incidence:ℚ)/
      (problemWeights p a tail).denominator := by
  simpa only [problemWeights,Scope.weights,Nat.cast_mul,Nat.cast_ofNat] using
    Weights.ofFractions_incidence p.incidences (p.s*(a::tail).length^2) p.n (2*p.r)
      (Nat.mul_pos p.hs (pow_pos (by simp) 2)) (Nat.mul_pos (by decide) p.hr)

theorem problem_computed_energies (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) :
    Packing.energy (Packing.incidenceType
      (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
      (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
      (problemAssignment p a tail)) ≤ (problemX p)^2 ∧
    Packing.headEnergy (problemAssignment p a tail) ≤ ((p.n:ℚ)/(2*(p.r:ℚ)))^2 := by
  let : NeZero p.r := ⟨Nat.ne_of_gt p.hr⟩
  let own := PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le
  let fac := PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le
  let ts := Scope.terms p.scopes p.n p.mask p.Q
  let ids := PackingIncidenceInput.Semantics.seedIndices p.n p.factors
  let eps : ℚ := 1/p.s
  have hs : (0:ℚ) < p.s := by exact_mod_cast p.hs
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hbig : 4*((B+b:ℕ):ℚ)*(Fintype.card (UniversalType p.r p.Q 1):ℚ)^2 ≤
      eps^2*(p.incidences:ℚ) := by
    have hc : Fintype.card (UniversalType p.r p.Q 1)=p.r^(2*p.Q) := by
      simp [Nat.mul_comm]
    have hh : (4*((B+b:ℕ):ℚ)*(Fintype.card (UniversalType p.r p.Q 1):ℚ)^2)*
        (p.s:ℚ)^2 ≤ p.incidences := by rw [hc]; exact_mod_cast hlarge
    calc
      _ ≤ (p.incidences:ℚ)/(p.s:ℚ)^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr hh
      _ = _ := by dsimp [eps]; ring
  have hg := Packing.computedWords_energies own fac a tail haN haC ts
    (scope_terms_nodup p.scopes p.n p.mask p.Q)
    (scope_terms_complete p.scopes p.n p.mask p.Q) ids
    (Packing.headsFirst_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _))
    (PackingIncidenceInput.Semantics.seedIndices_complete _ _) eps heps B b hB hb
    (by simpa only [Fintype.card_fin, PackingCallerProgram.Problem.incidences] using hM)
    (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [Fintype.card_fin, PackingCallerProgram.Problem.incidences] using hbig)
    (by norm_cast; simpa only [Fintype.card_fin] using hhead)
  simpa only [problemAssignment,problemX,ids,eps,own,fac,ts,Fintype.card_fin,
    PackingCallerProgram.Problem.incidences] using hg

theorem problem_head_max_bound (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) (low : Fin p.n → Bool) :
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) := by
  have hg := problem_computed_energies p a tail haN haC B b hB hb hM hn hlarge hhead
  apply source_max_le_of_energy
    (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
    (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
    a tail (Scope.terms p.scopes p.n p.mask p.Q) (problemWeights p a tail) (problemX p) p.hr
    (problem_weight_incidence p a tail) (problem_weight_head p a tail haN haC) low
  exact hg.2

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
