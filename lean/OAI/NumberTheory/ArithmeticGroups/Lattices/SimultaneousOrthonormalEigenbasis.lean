import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSelfAdjointCombination

/-! # Simultaneous Orthonormal Eigenbasis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SimultaneousOrthonormalEigenbasis.Construction

noncomputable section

/-! A commuting family of real self-adjoint operators has a common
orthonormal eigenbasis, including families with an infinite index type. -/

open scoped Classical
open _root_.Module.End

theorem exists_simultaneous_orthonormal_eigenbasis
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (T : ι → L →ₗ[ℝ] L) (hT : ∀ i, (T i).IsSymmetric)
    (hc : Pairwise (fun i j => Commute (T i) (T j))) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℝ L)) ℝ L)
      (w : Fin (Module.finrank ℝ L) → ι → ℝ), ∀ i j, T j (b i) = w i j • b i := by
  let P : (ι → ℝ) → Submodule ℝ L := fun χ => ⨅ j, eigenspace (T j) (χ j)
  have horth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have hind : iSupIndep P := horth.independent
  let J := {χ : ι → ℝ // P χ ≠ ⊥}
  let : Fintype J := hind.fintypeNeBotOfFiniteDimensional
  let Q : J → Submodule ℝ L := fun χ => P χ.val
  have hQorth : OrthogonalFamily ℝ (fun χ => Q χ) (fun χ => (Q χ).subtypeₗᵢ) :=
    horth.comp Subtype.val_injective
  have htop : (⨆ χ, Q χ) = ⊤ := by
    change (⨆ χ : {χ : ι → ℝ // P χ ≠ ⊥}, P χ.val) = ⊤
    rw [iSup_ne_bot_subtype]
    exact LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hc
  have hint : DirectSum.IsInternal Q := hQorth.isInternal_iff.mpr (by rw [htop, Submodule.top_orthogonal_eq_bot])
  let b := hint.subordinateOrthonormalBasis rfl hQorth
  let w : Fin (Module.finrank ℝ L) → ι → ℝ := fun i =>
    (hint.subordinateOrthonormalBasisIndex rfl i hQorth).val
  refine ⟨b, w, fun i j => ?_⟩
  have hi := hint.subordinateOrthonormalBasis_subordinate rfl i hQorth
  exact mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hi j)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SimultaneousOrthonormalEigenbasis.Construction
