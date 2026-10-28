import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Section Ideal Punctured Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover

noncomputable section

/-! Equations for an actual ideal sheaf give the principal cover
of its punctured affine neighborhood and the required excision cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v
variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type v} (a : ι → Γ(X, U)) (ha : Ideal.span (Set.range a) = I.ideal ⟨U, hU⟩)

def outside : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩

include ha in
theorem cover : U ⊓ outside I = ⨆ i, X.basicOpen (a i) := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hxI⟩ := hx
    apply Opens.mem_iSup.mpr
    by_contra! h
    apply hxI
    apply (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hxU).2
    rw [← ha, Scheme.zeroLocus_span]
    apply (X.mem_zeroLocus_iff _ x).2
    rintro _ ⟨i, rfl⟩
    exact h i
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hxU := X.basicOpen_le (a i) hi
    refine ⟨hxU, ?_⟩
    intro hxI
    have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hxU).1 hxI
    rw [← ha, Scheme.zeroLocus_span] at hz
    exact (X.mem_zeroLocus_iff _ x).1 hz (a i) (Set.mem_range_self i) hi

include ha in
theorem basicOpen_le (i : ι) : X.basicOpen (a i) ≤ outside I :=
  (le_iSup (fun j => X.basicOpen (a j)) i).trans
    ((cover I U hU a ha).symm.le.trans inf_le_right)

theorem global (hI : (I.support : Set X) ⊆ U) : U ⊔ outside I = ⊤ := by
  classical
  ext x
  change (x ∈ U ∨ x ∉ I.support) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    by_cases hx : x ∈ U
    · exact Or.inl hx
    · exact Or.inr (fun h => hx (hI h))

variable {T : Scheme.{u}} (s : T ⟶ X) [IsClosedImmersion s]

theorem section_global (h : ⊤ ≤ s ⁻¹ᵁ U) : U ⊔ outside s.ker = ⊤ := by
  apply global s.ker U
  intro x hx
  rw [Scheme.Hom.support_ker, s.isClosedEmbedding.isClosed_range.closure_eq] at hx
  obtain ⟨t, rfl⟩ := hx
  exact h (by trivial)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover
