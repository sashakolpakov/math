import OAI.RepresentationTheory.Theta.Geometric.AwayLattice

/-! # Principal Away Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A principal congruence on the original lattice extends to that same
lattice after inverting q, with the original full-level modulus. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.principal_preserves_awayLattice (g : D.RationalSU)
    (hg : ∀ x, x ∈ D.pel.reference.lattice ↔ D.rationalLinear g x ∈ D.pel.reference.lattice)
    (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : x ∈ D.awayLattice ↔ D.rationalLinear g x ∈ D.awayLattice := by
  rw [D.mem_awayLattice_iff, D.mem_awayLattice_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← map_zsmul]
    exact (hg _).mp hn
  · rintro ⟨n, hn⟩
    refine ⟨n, (hg _).mpr ?_⟩
    rwa [map_zsmul]

theorem Data.ActiveHeckeThetaData.principal_away_congruence (g : D.RationalSU)
    (hg : ∀ x ∈ D.pel.reference.lattice, ∃ y ∈ D.pel.reference.lattice,
      D.rationalLinear g x - x = D.pel.level • y)
    (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hx : x ∈ D.awayLattice) :
    ∃ y ∈ D.awayLattice, D.rationalLinear g x - x = D.pel.level • y := by
  obtain ⟨n, hn⟩ := (D.mem_awayLattice_iff x).mp hx
  obtain ⟨y, hy, he⟩ := hg ((q : ℤ) ^ n • x) hn
  rw [map_zsmul, ← smul_sub] at he
  let c : ℚ := (q : ℚ) ^ n
  have hc : c ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  let w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := c⁻¹ • y
  have hw : (q : ℤ) ^ n • w = y := by
    rw [← Nat.cast_pow, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_pow]
    change c • (c⁻¹ • y) = y
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  refine ⟨w, (D.mem_awayLattice_iff w).mpr ⟨n, hw.symm ▸ hy⟩, ?_⟩
  have h := congrArg (fun u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E => c⁻¹ • u) he
  rw [← Nat.cast_pow, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_pow] at h
  change c⁻¹ • (c • (D.rationalLinear g x - x)) = c⁻¹ • (D.pel.level • y) at h
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_comm] at h
  exact h

theorem Data.ActiveHeckeThetaData.principal_mem_rationalAwayLevel (g : D.RationalSU)
    (hg : ∀ x, x ∈ D.pel.reference.lattice ↔ D.rationalLinear g x ∈ D.pel.reference.lattice)
    (hc : ∀ x ∈ D.pel.reference.lattice, ∃ y ∈ D.pel.reference.lattice,
      D.rationalLinear g x - x = D.pel.level • y) : g ∈ D.rationalAwayLevel :=
  ⟨D.principal_preserves_awayLattice g hg, D.principal_away_congruence g hc⟩

end

end OAI.RepresentationTheory.Theta.Geometric
