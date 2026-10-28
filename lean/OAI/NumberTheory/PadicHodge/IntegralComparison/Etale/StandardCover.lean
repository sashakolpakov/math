import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Standard Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.StandardCover

noncomputable section

/-! Every etale algebra has an actual finite principal cover by
standard-etale presentations over its original coefficient ring. -/

universe u v
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A]

theorem exists_finite_cover : ∃ s : Finset A,
    (∀ a ∈ s, Algebra.IsStandardEtale R (Localization.Away a)) ∧ Ideal.span (s : Set A) = ⊤ := by
  apply Principal.OpenCover.finite_unit_family
  intro p
  obtain ⟨a, ha, he⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) p.asIdeal
  exact ⟨a, he, ha⟩

def localizers : Finset A := (exists_finite_cover R A).choose

theorem standard (a : localizers R A) : Algebra.IsStandardEtale R (Localization.Away a.val) :=
  (exists_finite_cover R A).choose_spec.1 a.val a.property

theorem span : Ideal.span (Set.range (fun a : localizers R A => a.val)) = ⊤ := by
  have he : Set.range (fun a : localizers R A => a.val) = (localizers R A : Set A) := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun ha => ⟨⟨x, ha⟩, rfl⟩⟩
  rw [he]
  exact (exists_finite_cover R A).choose_spec.2

def presentation (a : localizers R A) : StandardEtalePresentation R (Localization.Away a.val) := by
  let : Algebra.IsStandardEtale R (Localization.Away a.val) := standard R A a
  exact Classical.choice inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.StandardCover
