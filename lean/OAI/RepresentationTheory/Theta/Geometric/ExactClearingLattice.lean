import OAI.RepresentationTheory.Theta.Geometric.Cleared.LocalMatrices
import OAI.RepresentationTheory.Theta.Geometric.Local.TraceB
import OAI.RepresentationTheory.Theta.Geometric.Local.MatrixLattice

/-! # Exact Clearing Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The exact TateComparison clearing exponent clears the entire original lattice
for every active rational representative preserving the full away level. -/

set_option backward.isDefEq.respectTransparency false
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.cleared_localMatrix_opposite_entries (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (g : D.RationalSU)
    (v : Fin s × Bool) (n : ℕ)
    (hinv : ∀ i j, ‖(q : ℚ_[q]) ^ n * (D.localMatrix v g⁻¹).val i j‖ ≤ 1) :
    ∀ i j, ‖(q : ℚ_[q]) ^ n * (D.localMatrix (v.1, !v.2) g).val i j‖ ≤ 1 := by
  intro i j
  have hu (k : Fin 3) : ‖(if k = 2 then D.localEmbedding v D.pel.reference.b else 1)‖ = 1 := by
    split_ifs
    · exact D.localEmbedding_b_norm hg hc hgood hdegree v
    · exact norm_one
  have he := congrArg (fun a : ℚ_[q] => ‖a‖) (D.localMatrix_opposite_entry hc hgood g v i j)
  rw [norm_mul, norm_mul, hu, hu, one_mul, one_mul] at he
  simpa only [norm_mul, he] using hinv j i

theorem Data.ActiveHeckeThetaData.active_doubleCoset_cleared_local_entries (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (a : Intrinsic.Hecke.ActiveWeight) (g : D.RationalSU)
    (haway : D.away g ∈ D.awayLevel)
    (hcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹ (D.activeLocal g)⁻¹) :
    ∀ v i j, ‖(q : ℚ_[q]) ^ Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a *
      (D.localMatrix v g).val i j‖ ≤ 1 := by
  let n := Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a
  have hgcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a) (D.activeLocal g) := by
    simpa only [inv_inv] using Cleared.LocalMatrices.inDoubleCoset_inv (SphericalGU.Spherical.integralSL3 q) hcos
  have hactive := Cleared.LocalMatrices.scaled_doubleCoset_entries q n _ _
    (Cleared.LocalMatrices.active_representative_cleared_entries q D.pel.reference.distinguished a) hgcos
  have hinv := Cleared.LocalMatrices.scaled_doubleCoset_entries q n _ _
    (Cleared.LocalMatrices.active_representative_inverse_cleared_entries q D.pel.reference.distinguished a) hcos
  intro v
  by_cases hv : v.1 = D.pel.reference.distinguished
  · rcases v with ⟨v, side⟩
    dsimp at hv
    subst v
    cases side
    · exact hactive
    · apply D.cleared_localMatrix_opposite_entries hg hc hgood hdegree g
        (D.pel.reference.distinguished, false) n
      change ∀ i j, ‖(q : ℚ_[q]) ^ n * (D.activeLocal g⁻¹).val i j‖ ≤ 1
      simpa only [map_inv] using hinv
  · have hi := (AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_entries q _).mp (((hc.2.2 g).mp haway).2 v hv)
    intro i j
    rw [norm_mul]
    have hq : ‖(q : ℚ_[q]) ^ n‖ ≤ 1 := by
      have H := (AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan.q_zpow_integral_iff q (n : ℤ)).mpr (Int.natCast_nonneg n)
      obtain ⟨b, hb⟩ := H
      rw [zpow_natCast] at hb
      rw [← hb]
      exact b.property
    exact (mul_le_mul hq (hi i j) (norm_nonneg _) zero_le_one).trans (by simp)

theorem Data.ActiveHeckeThetaData.scaled_local_entries_preserve_reference (hc : D.HasFiniteCoordinates)
    (g : D.RationalSU) (v : Fin s × Bool) (n : ℕ)
    (hn : ∀ i j, ‖(q : ℚ_[q]) ^ n * (D.localMatrix v g).val i j‖ ≤ 1)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ D.pel.reference.lattice) :
    (fun i => D.localEmbedding v (((q : ℤ) ^ n • D.rationalLinear g u) i)) ∈
      Data.ActiveHeckeThetaData.standardLocalLattice (q := q) := by
  have hi : ∀ i, ‖D.localEmbedding v (u i)‖ ≤ 1 := by
    apply (Local.MatrixLattice.standardLocalLattice_mem_iff q _).mp
    rw [← hc.2.1 v]
    exact Submodule.subset_span ⟨u, hu, rfl⟩
  have H := AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralSymplectic.Local.padic_matrix_mulVec_integral q ((q : ℚ_[q]) ^ n • (D.localMatrix v g).val)
    hn (fun i => D.localEmbedding v (u i)) hi
  apply (Local.MatrixLattice.standardLocalLattice_mem_iff q _).mpr
  intro i
  have he : D.localEmbedding v (((q : ℤ) ^ n • D.rationalLinear g u) i) =
      (((q : ℚ_[q]) ^ n • (D.localMatrix v g).val).mulVec
        (fun j => D.localEmbedding v (u j))) i := by
    rw [Matrix.smul_mulVec, D.localMatrix_reference_action]
    change D.localEmbedding v ((q : ℤ) ^ n • D.rationalLinear g u i) = _
    rw [map_zsmul, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
    rfl
  rw [he]
  exact H i

theorem Data.ActiveHeckeThetaData.active_doubleCoset_exact_clearing (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (a : Intrinsic.Hecke.ActiveWeight) (g : D.RationalSU)
    (haway : D.away g ∈ D.awayLevel)
    (hcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹ (D.activeLocal g)⁻¹) :
    ∀ u ∈ D.pel.reference.lattice,
      (q : ℤ) ^ Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a • D.rationalLinear g u ∈
        D.pel.reference.lattice := by
  intro u hu
  apply D.referenceLattice_of_local_and_away hg hc hgood hdegree
  · intro v
    exact D.scaled_local_entries_preserve_reference hc g v _
      (D.active_doubleCoset_cleared_local_entries hg hc hgood hdegree a g haway hcos v) u hu
  · apply D.awayLattice.smul_mem
    exact (D.mem_awayLattice_iff _).mpr (D.away_level_clears_vector hc g haway ⟨u, hu⟩)

end

end OAI.RepresentationTheory.Theta.Geometric
