import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Superlattice
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryUniqueness

/-! # Relative Position From Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionFromKernel

noncomputable section

/-! Read the actual finite quotient type as a relative lattice position.
Only TateComparison's stated elementary-divisor input is used. The quotient calculation
and uniqueness of rank-three elementary groups are the checked IsogenyQuotient proofs. -/

theorem relativePosition_of_quotient_type (q : ℕ) [Fact q.Prime]
    (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (L M : Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (hLM : L.val ≤ M.val)
    (a : Fin 3 → ℕ) (ha : Antitone a)
    (hgroup : M.val ⧸ (L.val.comap M.val.subtype).toAddSubgroup ≃+
      (∀ i : Fin 3, ZMod (q ^ a i))) :
    Duality.RelativePosition (q : ℤ_[q]) (fun i => (a i : ℤ)) L M := by
  obtain ⟨b, ⟨hb, e, hL, hM⟩, _⟩ := hElementaryDivisors (q : ℤ_[q]) PadicInt.irreducible_p
    L.val M.val L.property M.property
  change M.val = IsogenyQuotient.LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e b at hM
  have hdiag : IsogenyQuotient.LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun _ => 0) ≤ IsogenyQuotient.LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e b := by
    rw [IsogenyQuotient.LatticeBounds.Construction.diagonalLattice_zero, ← hL, ← hM]
    exact hLM
  have hnonpos := (IsogenyQuotient.LatticeBounds.Construction.diagonalLattice_le_iff (q : ℤ_[q]) PadicInt.irreducible_p e (fun _ => 0) b).mp hdiag
  let c : Fin 3 → ℕ := fun i => (-b i).toNat
  have hc (i : Fin 3) : (c i : ℤ) = -b i := Int.toNat_of_nonneg (neg_nonneg.mpr (hnonpos i))
  have hcanti : Antitone c := by
    intro i j hij
    apply Int.ofNat_le.mp
    rw [hc, hc]
    exact neg_le_neg (hb hij)
  have hneg : (fun i => -(c i : ℤ)) = b := by
    funext i
    rw [hc, neg_neg]
  have hM' : M.val = IsogenyQuotient.LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(c i : ℤ)) := by
    rw [hneg]
    exact hM
  have htype := IsogenyQuotient.Superlattice.Construction.superlatticeQuotientEquiv q L.val M.val hLM e c hL hM'
  have hac : a = c := IsogenyQuotient.ElementaryUniqueness.Construction.rankThree_elementary_exponents_unique q Fact.out a c ha hcanti
    (hgroup.symm.trans htype)
  refine ⟨e, hL, ?_⟩
  change M.val = IsogenyQuotient.LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))
  rw [hac]
  exact hM'

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionFromKernel
