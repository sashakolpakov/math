import OAI.NumberTheory.ArithmeticGroups.Lattices.SimultaneousOrthonormalEigenbasis

/-! # Invariant Symmetric Eigenspaces -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSymmetricEigenspaces.Construction

noncomputable section

/-! An invariant subspace of a symmetric operator is spanned by the
eigenvectors it contains. -/

open _root_.Module.End

theorem symmetric_invariant_subspace_eigenspace_span
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] V) (hA : A.IsSymmetric) (P : Submodule ℝ V)
    (hP : ∀ x ∈ P, A x ∈ P) : P = ⨆ r : ℝ, P ⊓ eigenspace A r := by
  let Q := ⨆ r : ℝ, P ⊓ eigenspace A r
  have hr := hA.restrict_invariant hP
  have htop : (⨆ r : ℝ, eigenspace (A.restrict hP) r) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hr.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hle : (⨆ r : ℝ, eigenspace (A.restrict hP) r) ≤ Q.comap P.subtype := by
    apply iSup_le
    intro r x hx
    change x.val ∈ Q
    apply Submodule.mem_iSup_of_mem r
    refine ⟨x.property, mem_eigenspace_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_eigenspace_iff.mp hx)
  rw [htop] at hle
  apply le_antisymm
  · intro x hx
    exact hle (show (⟨x, hx⟩ : P) ∈ (⊤ : Submodule ℝ P) from trivial)
  · exact iSup_le (fun _ => inf_le_left)

theorem equiv_symmetric_invariant_eigenspace_span
    {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ : V ≃ₗ[ℝ] E) (A : V →ₗ[ℝ] V) (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hΦ : ∀ x, T (Φ x) = Φ (A x)) (P : Submodule ℝ V)
    (hP : ∀ x ∈ P, A x ∈ P) : P = ⨆ r : ℝ, P ⊓ eigenspace A r := by
  let Q := P.map Φ.toLinearMap
  have hQ : ∀ y ∈ Q, T y ∈ Q := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change T (Φ x) ∈ Q
    rw [hΦ]
    exact Submodule.mem_map_of_mem (hP x hx)
  have hspan := symmetric_invariant_subspace_eigenspace_span T hT Q hQ
  let S := ⨆ r : ℝ, P ⊓ eigenspace A r
  have hle : Q ≤ S.map Φ.toLinearMap := by
    rw [hspan]
    apply iSup_le
    intro r y hy
    obtain ⟨x, hx, rfl⟩ := hy.1
    apply Submodule.mem_map_of_mem
    apply Submodule.mem_iSup_of_mem r
    refine ⟨hx, mem_eigenspace_iff.mpr ?_⟩
    apply Φ.injective
    rw [← hΦ, map_smul]
    exact mem_eigenspace_iff.mp hy.2
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, he⟩ := hle (Submodule.mem_map_of_mem (f := Φ.toLinearMap) hx)
    have hxy : y = x := Φ.injective he
    exact hxy ▸ hy
  · exact iSup_le (fun _ => inf_le_left)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSymmetricEigenspaces.Construction
