import OAI.RepresentationTheory.Theta.Geometric.Data

/-! # Away Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Membership in the reference lattice with q inverted is literal
clearing by a power of q. Finite generation gives one clearing exponent
for an entire integral lattice map. -/

variable {V : Type*} [AddCommGroup V]

theorem AwayLattice.power_clearing_add (q : ℕ) (L : Submodule ℤ V) {u v : V}
    (hu : ∃ n : ℕ, (q : ℤ) ^ n • u ∈ L)
    (hv : ∃ n : ℕ, (q : ℤ) ^ n • v ∈ L) :
    ∃ n : ℕ, (q : ℤ) ^ n • (u + v) ∈ L := by
  obtain ⟨m, hm⟩ := hu
  obtain ⟨n, hn⟩ := hv
  refine ⟨m + n, ?_⟩
  rw [smul_add]
  apply L.add_mem
  · rw [Nat.add_comm m n, pow_add, mul_smul]
    exact L.smul_mem _ hm
  · rw [pow_add, mul_smul]
    exact L.smul_mem _ hn

theorem AwayLattice.mem_power_localized_lattice (q : ℕ) (L : Submodule ℤ V) (v : V) :
    v ∈ Submodule.span ℤ {u | ∃ n : ℕ, (q : ℤ) ^ n • u ∈ L} ↔
      ∃ n : ℕ, (q : ℤ) ^ n • v ∈ L := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem u hu => exact hu
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv => exact AwayLattice.power_clearing_add q L hu hv
    | smul c u _ hu =>
      obtain ⟨n, hn⟩ := hu
      refine ⟨n, ?_⟩
      rw [smul_comm]
      exact L.smul_mem c hn
  · intro h
    exact Submodule.subset_span h

theorem AwayLattice.finite_set_power_clearing (q : ℕ) (L : Submodule ℤ V)
    (S : Finset V) (f : V → V)
    (h : ∀ v ∈ S, ∃ n : ℕ, (q : ℤ) ^ n • f v ∈ L) :
    ∃ n : ℕ, ∀ v ∈ S, (q : ℤ) ^ n • f v ∈ L := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert v S hv ih =>
    obtain ⟨m, hm⟩ := h v (Finset.mem_insert_self v S)
    obtain ⟨n, hn⟩ := ih (fun w hw => h w (Finset.mem_insert_of_mem hw))
    refine ⟨m + n, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rw [Nat.add_comm m n, pow_add, mul_smul]
      exact L.smul_mem _ hm
    · rw [pow_add, mul_smul]
      exact L.smul_mem _ (hn w hw)

theorem AwayLattice.fg_lattice_power_clearing (q : ℕ) (L M : Submodule ℤ V)
    (hL : L.FG) (f : V →ₗ[ℤ] V)
    (h : ∀ v ∈ L, ∃ n : ℕ, (q : ℤ) ^ n • f v ∈ M) :
    ∃ n : ℕ, ∀ v ∈ L, (q : ℤ) ^ n • f v ∈ M := by
  obtain ⟨S, hS⟩ := hL
  obtain ⟨n, hn⟩ := AwayLattice.finite_set_power_clearing q M S f (fun v hv =>
    h v (by rw [← hS]; exact Submodule.subset_span hv))
  have hle : L ≤ M.comap ((q : ℤ) ^ n • f) := by
    rw [← hS]
    apply Submodule.span_le.mpr
    exact hn
  exact ⟨n, fun v hv => hle hv⟩

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.mem_awayLattice_iff (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    v ∈ D.awayLattice ↔ ∃ n : ℕ, (q : ℤ) ^ n • v ∈ D.pel.reference.lattice :=
  AwayLattice.mem_power_localized_lattice q D.pel.reference.lattice v

theorem Data.ActiveHeckeThetaData.reference_mem_awayLattice {v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E} (hv : v ∈ D.pel.reference.lattice) :
    v ∈ D.awayLattice :=
  (D.mem_awayLattice_iff v).mpr ⟨0, by simpa only [pow_zero, one_smul] using hv⟩

theorem Data.ActiveHeckeThetaData.away_level_clears_vector (hc : D.HasFiniteCoordinates) (g : D.RationalSU)
    (hg : D.away g ∈ D.awayLevel) (v : D.pel.reference.lattice) :
    ∃ n : ℕ, (q : ℤ) ^ n • D.rationalLinear g v.val ∈ D.pel.reference.lattice := by
  have hm := ((hc.2.2 g).mp hg).1
  change D.rationalLinear g ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup D.awayLattice.toAddSubgroup D.pel.level at hm
  apply (D.mem_awayLattice_iff _).mp
  exact (hm.1 v.val).mp (D.reference_mem_awayLattice v.property)

theorem Data.ActiveHeckeThetaData.away_level_clears_lattice (hgeometry : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (g : D.RationalSU) (hg : D.away g ∈ D.awayLevel) :
    ∃ n : ℕ, ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice := by
  rcases hgeometry.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, hL, _⟩
  apply AwayLattice.fg_lattice_power_clearing q _ _ hL.1 ((D.rationalLinear g).toLinearMap.restrictScalars ℤ)
  intro v hv
  exact D.away_level_clears_vector hc g hg ⟨v, hv⟩

end

end OAI.RepresentationTheory.Theta.Geometric
