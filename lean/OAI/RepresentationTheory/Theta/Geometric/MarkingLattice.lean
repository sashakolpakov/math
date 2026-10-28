import OAI.RepresentationTheory.Theta.Geometric.AwayLattice

/-! # Marking Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Clearing an away-principal rational matrix retains its prescribed
full-level congruence on the original integral reference lattice. -/

theorem MarkingLattice.localized_lattice_saturation {V : Type*} [AddCommGroup V]
    (L : Submodule ℤ V) (q N : ℕ) (hcop : Nat.Coprime q N) (u : V)
    (hu : ∃ m : ℕ, (q : ℤ) ^ m • u ∈ L) (hN : (N : ℤ) • u ∈ L) : u ∈ L := by
  obtain ⟨m, hm⟩ := hu
  have hbez : (q : ℤ) ^ m * Nat.gcdA (q ^ m) N + (N : ℤ) * Nat.gcdB (q ^ m) N = 1 := by
    rw [← Nat.cast_pow, ← Nat.gcd_eq_gcd_ab, (hcop.pow_left m).gcd_eq_one]
    rfl
  have h := L.add_mem (L.smul_mem (Nat.gcdA (q ^ m) N) hm)
    (L.smul_mem (Nat.gcdB (q ^ m) N) hN)
  convert h using 1
  rw [smul_smul, smul_smul, ← add_smul, mul_comm (Nat.gcdA (q ^ m) N),
    mul_comm (Nat.gcdB (q ^ m) N), hbez, one_smul]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.cleared_away_level_congruence (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hc : D.HasFiniteCoordinates) (g : D.RationalSU) (ha : D.away g ∈ D.awayLevel)
    (n : ℕ) (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hv : v ∈ D.pel.reference.lattice) :
    ∃ w ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v - (q : ℤ) ^ n • v = (D.pel.level : ℤ) • w := by
  have h := ((hc.2.2 g).mp ha).1
  change D.rationalLinear g ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup D.awayLattice.toAddSubgroup D.pel.level at h
  obtain ⟨w, hw, hrel⟩ := h.2 v (D.reference_mem_awayLattice hv)
  let c : ℤ := (q : ℤ) ^ n
  have hcaway : c • w ∈ D.awayLattice := D.awayLattice.smul_mem c hw
  have hN : (D.pel.level : ℤ) • (c • w) ∈ D.pel.reference.lattice := by
    rw [smul_comm, natCast_zsmul, ← hrel, smul_sub]
    exact D.pel.reference.lattice.sub_mem (hn v hv) (D.pel.reference.lattice.smul_mem c hv)
  have hint : c • w ∈ D.pel.reference.lattice :=
    MarkingLattice.localized_lattice_saturation D.pel.reference.lattice q D.pel.level hgood.2.2.1 (c • w)
      ((D.mem_awayLattice_iff _).mp hcaway) hN
  refine ⟨c • w, hint, ?_⟩
  change c • D.rationalLinear g v - c • v = (D.pel.level : ℤ) • (c • w)
  rw [← smul_sub, hrel, natCast_zsmul, smul_comm]

end

end OAI.RepresentationTheory.Theta.Geometric
