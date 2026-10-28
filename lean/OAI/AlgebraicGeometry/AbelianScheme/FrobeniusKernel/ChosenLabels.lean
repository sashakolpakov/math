import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import Mathlib.Data.Fintype.EquivFin

/-! # Chosen Labels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenLabels.Construction

noncomputable section

/-!
Enumerate the actual CMPoints chosen conjugate representatives, with the
active conjugation label first. The paired enumeration is constructed
from the chosen set and its conjugation-complement property.
-/

section Representatives

variable {G : Type*} [Group G] (c : G) (hcc : c * c = 1)
variable (chosen : Set G) (hchosen : ∀ τ, τ ∈ chosen ↔ c * τ ∉ chosen)

def chosenPairEquiv : (chosen × Bool) ≃ G :=
  Equiv.ofBijective (fun p => if p.2 then c * p.1.val else p.1.val) (by
    constructor
    · intro ⟨a, b⟩ ⟨a', b'⟩ h
      cases b <;> cases b'
      · exact Prod.ext (Subtype.ext h) rfl
      · change a.val = c * a'.val at h
        exact False.elim ((hchosen a').mp a'.property (h ▸ a.property))
      · change c * a.val = a'.val at h
        exact False.elim ((hchosen a).mp a.property (h.symm ▸ a'.property))
      · exact Prod.ext (Subtype.ext (mul_left_cancel h)) rfl
    · intro τ
      by_cases h : τ ∈ chosen
      · exact ⟨(⟨τ, h⟩, false), rfl⟩
      · have hi : c * (c * τ) = τ := by rw [← mul_assoc, hcc, one_mul]
        exact ⟨(⟨c * τ, (hchosen (c * τ)).mpr (hi.symm ▸ h)⟩, true), hi⟩)

theorem chosenPairEquiv_false (τ : chosen) :
    chosenPairEquiv c hcc chosen hchosen (τ, false) = τ.val := rfl

theorem chosenPairEquiv_true (τ : chosen) :
    chosenPairEquiv c hcc chosen hchosen (τ, true) = c * τ.val := rfl

variable [Fintype chosen] {s : ℕ} (hcard : Fintype.card chosen = s + 1) (hc : c ∈ chosen)

def chosenEnumeration : Fin (s + 1) ≃ chosen :=
  (Equiv.swap 0 ((Fintype.equivFinOfCardEq hcard) ⟨c, hc⟩)).trans
    (Fintype.equivFinOfCardEq hcard).symm

omit [Group G] in
theorem chosenEnumeration_zero : chosenEnumeration c chosen hcard hc 0 = ⟨c, hc⟩ := by
  simp only [chosenEnumeration, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.symm_apply_apply]

def chosenLabels : (Fin (s + 1) × Bool) ≃ G :=
  (Equiv.prodCongr (chosenEnumeration c chosen hcard hc) (Equiv.refl Bool)).trans
    (chosenPairEquiv c hcc chosen hchosen)

theorem chosenLabels_active : chosenLabels c hcc chosen hchosen hcard hc (0, false) = c :=
  congrArg Subtype.val (chosenEnumeration_zero c chosen hcard hc)

theorem chosenLabels_conjugate (v : Fin (s + 1)) :
    chosenLabels c hcc chosen hchosen hcard hc (v, true) =
      c * chosenLabels c hcc chosen hchosen hcard hc (v, false) := rfl

theorem chosenLabels_chosen (v : Fin (s + 1)) :
    chosenLabels c hcc chosen hchosen hcard hc (v, false) ∈ chosen :=
  (chosenEnumeration c chosen hcard hc v).property

theorem chosenLabels_opposite_not_chosen (v : Fin (s + 1)) :
    chosenLabels c hcc chosen hchosen hcard hc (v, true) ∉ chosen :=
  (hchosen _).mp (chosenLabels_chosen c hcc chosen hchosen hcard hc v)

end Representatives

open OAI.AlgebraicGeometry.PELModuli.CMPoints.Models

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

/-- No enumeration or conjugate-label compatibility is an extra input. -/
theorem exists_l45ChosenLabels (chosen : Set Gal(E/ℚ))
    (hc : PELModuli.CMPoints.Arithmetic.rationalConjugation E ∈ chosen)
    (hchosen : ∀ τ, τ ∈ chosen ↔ PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ ∉ chosen) :
    ∃ (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)),
      labels (0, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E ∧
      (∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false)) ∧
      (∀ v, labels (v, false) ∈ chosen) ∧
      (∀ v, labels (v, true) ∉ chosen) := by
  classical
  let : Fintype chosen := Fintype.ofFinite _
  have : Nonempty chosen := ⟨⟨PELModuli.CMPoints.Arithmetic.rationalConjugation E, hc⟩⟩
  let s := Fintype.card chosen - 1
  have hs : Fintype.card chosen = s + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
  let labels := chosenLabels (PELModuli.CMPoints.Arithmetic.rationalConjugation E)
    PELModuli.CMPoints.Models.rationalConjugation_mul_self chosen hchosen hs hc
  exact ⟨s, labels, chosenLabels_active _ _ _ _ _ _,
    chosenLabels_conjugate _ _ _ _ _ _, chosenLabels_chosen _ _ _ _ _ _,
    chosenLabels_opposite_not_chosen _ _ _ _ _ _⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenLabels.Construction
