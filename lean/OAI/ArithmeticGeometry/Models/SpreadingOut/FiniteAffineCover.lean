import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenOver
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite Affine Cover -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteAffineCover.Construction

noncomputable section

/-! Finite nonempty affine charts and their common dense open domain. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem finite_nonempty_affine_open_cover
    (X : Scheme.{u}) [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens),
      (∀ i, IsAffineOpen (V i) ∧ (V i : Set X).Nonempty) ∧ (⨆ i, V i) = ⊤ := by
  obtain ⟨Us, hUs, hfin, htop⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact
    (show IsCompact ((⊤ : X.Opens) : Set X) from isCompact_univ)
  let T : Set X.Opens := {V | V ∈ Us ∧ (V : Set X).Nonempty}
  have hT : T.Finite := hfin.subset (fun _ h ↦ h.1)
  let ι := T
  let : Finite ι := hT.to_subtype
  let V : ι → X.Opens := Subtype.val
  refine ⟨ι, inferInstance, V, ?_, ?_⟩
  · intro i
    exact ⟨hUs i.property.1, i.property.2⟩
  · apply top_unique
    intro x _
    have hx : x ∈ sSup Us := by rw [← htop]; trivial
    obtain ⟨A, hA, hxA⟩ := Opens.mem_sSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨A, hA, x, hxA⟩, hxA⟩

/-- Finitely many nonempty opens in an irreducible scheme have a common
dense open contained in all of them. -/
theorem common_dense_open
    (X : Scheme.{u}) [IrreducibleSpace X]
    {ι : Type u} [Finite ι] (V : ι → X.Opens) (hV : ∀ i, (V i : Set X).Nonempty) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ ∀ i, U ≤ V i := by
  let U := ⨅ i, V i
  have hη : genericPoint X ∈ U := by
    change genericPoint X ∈ (U : Set X)
    rw [Opens.coe_iInf]
    apply Set.mem_iInter.mpr
    intro i
    exact ((genericPoint_spec X).mem_open_set_iff (V i).isOpen).mpr
      (by simpa using hV i)
  exact ⟨U, U.isOpen.dense ⟨genericPoint X, hη⟩, fun i ↦ iInf_le V i⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteAffineCover.Construction
