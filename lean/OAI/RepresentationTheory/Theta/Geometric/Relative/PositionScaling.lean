import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices

/-! # Position Scaling -/

namespace OAI.RepresentationTheory.Theta.Geometric.Relative.PositionScaling

noncomputable section

/-! Exact scalar shifts and reversal of intrinsic rank-three lattice
positions, retaining simultaneous bases and their original q-powers. -/

open scoped Pointwise

variable (q : ℕ) [Fact q.Prime]

def scaledRankThreeLattice (r : ℤ) (L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q] :=
  AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionTransport.rankThreeLatticeEquiv (LinearEquiv.smulOfUnit (M := Fin 3 → ℚ_[q]) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ r)) L

theorem scaledRankThreeLattice_val (r : ℤ) (L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) :
    (scaledRankThreeLattice q r L).val = (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ r) • L.val := by
  ext x
  rfl

theorem relativePosition_scale_right (a : Fin 3 → ℤ) (r : ℤ)
    (L M : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (h : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) a L M) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) (fun i => a i - r) L (scaledRankThreeLattice q r M) := by
  obtain ⟨b, hL, hM⟩ := h
  refine ⟨b, hL, ?_⟩
  rw [scaledRankThreeLattice_val, hM]
  change ((AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ r : ℚ_[q]ˣ) : ℚ_[q]) • Submodule.span ℤ_[q] _ = _
  rw [Submodule.smul_span, Set.smul_set_range]
  congr 2
  funext i
  simp only [Units.val_zpow_eq_zpow_val, map_natCast]
  change (q : ℚ_[q]) ^ r • ((q : ℚ_[q]) ^ (-a i) • b i) =
    (q : ℚ_[q]) ^ (-(a i - r)) • b i
  rw [smul_smul, ← zpow_add₀ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)]
  congr 2
  omega

theorem relativePosition_swap (a : Fin 3 → ℤ)
    (L M : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (h : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) a L M) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) (fun i => -a i) M L := by
  obtain ⟨b, hL, hM⟩ := h
  refine ⟨b.unitsSMul (fun i => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (-a i)), ?_, ?_⟩
  · rw [hM]
    congr 2
    funext i
    rw [Module.Basis.unitsSMul_apply]
    simp only [Units.smul_def, Units.val_zpow_eq_zpow_val, map_natCast]
    rfl
  · rw [hL]
    congr 2
    funext i
    rw [Module.Basis.unitsSMul_apply]
    simp only [Units.smul_def, Units.val_zpow_eq_zpow_val, map_natCast]
    change b i = (q : ℚ_[q]) ^ (-(-a i)) • ((q : ℚ_[q]) ^ (-a i) • b i)
    rw [neg_neg, smul_smul, ← zpow_add₀ (by exact_mod_cast (Fact.out : q.Prime).ne_zero),
      add_neg_cancel, zpow_zero, one_smul]

theorem relativePosition_reindex (a : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3))
    (L M : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (h : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) a L M) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) (fun i => a (σ.symm i)) L M := by
  obtain ⟨b, hL, hM⟩ := h
  refine ⟨b.reindex σ, ?_, ?_⟩
  · rw [hL]
    congr 1
    simpa only [Module.Basis.coe_reindex] using (σ.symm.surjective.range_comp b).symm
  · rw [hM]
    congr 1
    simpa only [Module.Basis.reindex_apply, Function.comp_def, map_natCast] using
      (σ.symm.surjective.range_comp (fun i => (q : ℚ_[q]) ^ (-a i) • b i)).symm

theorem relativePosition_complement (a : Fin 3 → ℤ) (m : ℕ)
    (L M : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (h : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) a L M) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) (fun i => (m : ℤ) - a (Fin.rev i))
      M (scaledRankThreeLattice q (-(m : ℤ)) L) := by
  have H := relativePosition_reindex q _ Fin.revPerm _ _
    (relativePosition_scale_right q _ (-(m : ℤ)) _ _ (relativePosition_swap q a L M h))
  simpa only [Fin.revPerm_symm, Fin.revPerm_apply, sub_neg_eq_add, neg_add_eq_sub] using H

end

end OAI.RepresentationTheory.Theta.Geometric.Relative.PositionScaling
