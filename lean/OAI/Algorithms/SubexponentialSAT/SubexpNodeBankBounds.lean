import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixImageBounds
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankMap

namespace OAI.Algorithms

/-! Actual matrix-image bank bytes in terms of the layout's iteration count.
The counts follow from the enumeration equivalences, rather than from a
caller-supplied size certificate. -/

namespace SubexponentialSAT.SubexpNodeBankBounds

open scoped BigOperators
open Subexp.BlockCoefficientProgram Subexp.MatrixWordEncoding

abbrev Bits := List Bool

def vectorBytes (p : ℕ) {D : ℕ} (v : Fin D → ZMod p) : Bits :=
  (vectorWords p v).flatten

theorem vectorBytes_length (p : ℕ) {D : ℕ} (v : Fin D → ZMod p) :
    (vectorBytes p v).length = D * width p := by
  simp [vectorBytes, vectorWords, List.length_flatten, List.map_ofFn,
    Function.comp_def, Subexp.MatrixWordEncoding.word_length]

def bank (p : ℕ) {D n : ℕ} (v : Fin n → Fin D → ZMod p) : List Bits :=
  (List.ofFn v).map (vectorBytes p)

@[simp] theorem bank_length (p : ℕ) {D n : ℕ} (v : Fin n → Fin D → ZMod p) :
    (bank p v).length = n := by simp [bank]

theorem bank_encoded_length (p : ℕ) {D n : ℕ} (v : Fin n → Fin D → ZMod p) :
    (Encoding.encodeList id (bank p v)).length = (2*(D*width p)+2)*n+1 := by
  rw [SubexpRawTemplateBounds.encoded_length, bank_length]
  have hs : ((bank p v).map List.length).sum = n*(D*width p) := by
    simp [bank, Function.comp_def, vectorBytes_length]
  rw [hs]
  ring

section Layout

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {t : Fin c.Q}

def outerBanks (e : SubexpLayoutSpec.EnumerationData L t) : List Bits :=
  bank p e.outerBase

def innerBanks (e : SubexpLayoutSpec.EnumerationData L t) : List (List Bits) :=
  List.ofFn fun g => bank p (e.increment g)

def bankBundle (e : SubexpLayoutSpec.EnumerationData L t) : Bits :=
  SubexpRawTemplateBounds.bankMaster (outerBanks e) (innerBanks e)

theorem innerCount_pos (e : SubexpLayoutSpec.EnumerationData L t) (g : Fin r) :
    1 ≤ e.innerCount g := by
  rw [e.innerCount_eq]
  exact Nat.one_le_pow _ _ (Fact.out : p.Prime).pos

theorem outerCount_pos (e : SubexpLayoutSpec.EnumerationData L t) :
    1 ≤ e.outerCount := by
  rw [e.outerCount_eq]
  exact Nat.one_le_pow _ _ (Fact.out : p.Prime).pos

theorem colors_le_innerSum (e : SubexpLayoutSpec.EnumerationData L t) :
    r ≤ ∑ g, e.innerCount g := by
  calc
    r = ∑ _g : Fin r, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun g _ => innerCount_pos e g)

theorem innerSum_le_iterations (e : SubexpLayoutSpec.EnumerationData L t) :
    (∑ g, e.innerCount g) ≤ e.iterationCount := by
  simpa only [one_mul, SubexpLayoutSpec.EnumerationData.iterationCount] using
    Nat.mul_le_mul_right (∑ g, e.innerCount g) (outerCount_pos e)

theorem outerCount_le_iterations (e : SubexpLayoutSpec.EnumerationData L t) :
    e.outerCount ≤ e.iterationCount := by
  have hs : 1 ≤ ∑ g, e.innerCount g := by
    have hr := c.r_ge_two
    have h := colors_le_innerSum e
    omega
  simpa only [mul_one, SubexpLayoutSpec.EnumerationData.iterationCount] using
    Nat.mul_le_mul_left e.outerCount hs

theorem colors_le_iterations (e : SubexpLayoutSpec.EnumerationData L t) :
    r ≤ e.iterationCount := (colors_le_innerSum e).trans (innerSum_le_iterations e)

theorem bankBundle_length (e : SubexpLayoutSpec.EnumerationData L t) :
    (bankBundle e).length =
      4*(D*width p+1)*(e.outerCount + ∑ g, e.innerCount g)+4*r+5 := by
  rw [bankBundle, SubexpRawTemplateBounds.bankMaster_length]
  have ho : (SubexpRawTemplateBounds.encode (outerBanks e)).length =
      (2*(D*width p)+2)*e.outerCount+1 := bank_encoded_length p e.outerBase
  have hi : ((innerBanks e).map (fun xs => (SubexpRawTemplateBounds.encode xs).length)).sum =
      (2*(D*width p)+2)*(∑ g, e.innerCount g)+r := by
    simp only [innerBanks, List.map_ofFn, Function.comp_def, bank_encoded_length,
      List.sum_ofFn, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  rw [ho, hi]
  simp only [innerBanks, List.length_ofFn]
  ring

/-- One bound for the entire physically serialized outer/inner bundle. -/
theorem bankBundle_length_le (e : SubexpLayoutSpec.EnumerationData L t) :
    (bankBundle e).length ≤ 16*(D*width p+1)*(e.iterationCount+1) := by
  have ho := outerCount_le_iterations e
  have hi := innerSum_le_iterations e
  have hr := colors_le_iterations e
  rw [bankBundle_length]
  calc
    _ ≤ 4*(D*width p+1)*(2*e.iterationCount)+4*e.iterationCount+5 := by
      gcongr
      omega
    _ ≤ _ := by ring_nf; omega

end Layout

end SubexponentialSAT.SubexpNodeBankBounds

end OAI.Algorithms
