import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.SectionCechIndices
import Mathlib.Data.Finset.Sort

/-! # Finite Subsets -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.FiniteSubsets

noncomputable section

/-! Ordered Čech tuples correspond to finite subsets of the same size. -/

universe u

variable {ι : Type u} [LinearOrder ι]

def orderedCechIndexFinset {q : ℕ} (a : Ordered.SectionCechIndices.OrderedCechIndex ι q) : Finset ι :=
  Finset.univ.image a.val

theorem orderedCechIndexFinset_card {q : ℕ} (a : Ordered.SectionCechIndices.OrderedCechIndex ι q) :
    (orderedCechIndexFinset a).card = q + 1 := by
  rw [orderedCechIndexFinset, Finset.card_image_of_injective _ a.property.injective,
    Finset.card_univ, Fintype.card_fin]

def orderedCechIndexFinsetEquiv (ι : Type u) [LinearOrder ι] (q : ℕ) :
    Ordered.SectionCechIndices.OrderedCechIndex ι q ≃ {s : Finset ι // s.card = q + 1} where
  toFun a := ⟨orderedCechIndexFinset a, orderedCechIndexFinset_card a⟩
  invFun s := ⟨s.val.orderEmbOfFin s.property, (s.val.orderEmbOfFin s.property).strictMono⟩
  left_inv a := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique (orderedCechIndexFinset_card a)
      (fun k ↦ Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) a.property).symm
  right_inv s := by
    apply Subtype.ext
    change Finset.univ.image (s.val.orderEmbOfFin s.property) = s.val
    have h := Finset.map_orderEmbOfFin_univ s.val s.property
    rw [Finset.map_eq_image] at h
    exact h

theorem orderedCechIndexFinset_delete {q : ℕ} (a : Ordered.SectionCechIndices.OrderedCechIndex ι (q + 1))
    (k : Fin (q + 2)) :
    orderedCechIndexFinset (a.delete k) = (orderedCechIndexFinset a).erase (a.val k) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_erase.mpr
    constructor
    · change a.val (k.succAbove j) ≠ a.val k
      exact fun he ↦ Fin.succAbove_ne k j (a.property.injective he)
    · exact Finset.mem_image.mpr ⟨k.succAbove j, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hin
    have hj : j ≠ k := fun he ↦ hne (congrArg a.val he)
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hj
    apply Finset.mem_image.mpr
    refine ⟨l, Finset.mem_univ _, ?_⟩
    change a.val (k.succAbove l) = a.val j
    exact congrArg a.val hl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.FiniteSubsets
