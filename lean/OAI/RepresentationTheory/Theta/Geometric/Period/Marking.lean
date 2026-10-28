import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM
import OAI.RepresentationTheory.Theta.Geometric.MarkingLattice

/-! # Marking -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual N-division points defined by the fixed reference lattice
retain the full-level marking under a cleared rational SU isogeny. -/

theorem Period.Marking.fractional_lattice_congruence {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : AddSubgroup V) (N : ℕ) (hN : (N : ℂ) ≠ 0) (c : ℤ) (u v w : V)
    (hw : w ∈ L) (hrel : c • u - c • v = (N : ℤ) • w) :
    (QuotientAddGroup.mk ((N : ℂ)⁻¹ • (c • u)) : V ⧸ L) =
      c • QuotientAddGroup.mk ((N : ℂ)⁻¹ • v) := by
  have hvec : (N : ℂ)⁻¹ • (c • u) - c • ((N : ℂ)⁻¹ • v) = w := by
    rw [smul_comm c (N : ℂ)⁻¹, ← smul_sub, hrel, natCast_zsmul,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have hplus : (N : ℂ)⁻¹ • (c • u) = c • ((N : ℂ)⁻¹ • v) + w := by
    calc
      (N : ℂ)⁻¹ • (c • u) =
          ((N : ℂ)⁻¹ • (c • u) - c • ((N : ℂ)⁻¹ • v)) + c • ((N : ℂ)⁻¹ • v) :=
        (sub_add_cancel _ _).symm
      _ = w + c • ((N : ℂ)⁻¹ • v) := by rw [hvec]
      _ = c • ((N : ℂ)⁻¹ • v) + w := add_comm _ _
  rw [hplus, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero]
  exact map_zsmul (QuotientAddGroup.mk' L) c ((N : ℂ)⁻¹ • v)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.periodLevelPoint (x : D.domain) (v : D.pel.reference.lattice) :
    Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ⧸ D.periodLattice x.val :=
  QuotientAddGroup.mk ((D.pel.level : ℂ)⁻¹ • D.periodReferenceEmbedding x.val v.val)

theorem Data.ActiveHeckeThetaData.clearedPeriodTorusMap_marking (hg : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hc : D.HasFiniteCoordinates)
    (g : D.RationalSU) (ha : D.away g ∈ D.awayLevel) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (v : D.pel.reference.lattice) :
    D.clearedPeriodTorusMap hg g n hn x (D.periodLevelPoint x v) =
      (q : ℤ) ^ n • D.periodLevelPoint (D.rationalPeriodPoint g x) v := by
  let y := D.rationalPeriodPoint g x
  let c : ℤ := (q : ℤ) ^ n
  have hN : (D.pel.level : ℂ) ≠ 0 := by
    have h := hg.fullLevel
    exact_mod_cast (show D.pel.level ≠ 0 by omega)
  obtain ⟨w, hw, hrel⟩ := D.cleared_away_level_congruence hgood hc g ha n hn v.val v.property
  have hp := congrArg (D.periodReferenceEmbedding y.val) hrel
  simp only [map_sub, map_zsmul] at hp
  have hf : ((q : ℤ) ^ n • D.rationalPeriodLinear g x)
      ((D.pel.level : ℂ)⁻¹ • D.periodReferenceEmbedding x.val v.val) =
      (D.pel.level : ℂ)⁻¹ • (c • D.periodReferenceEmbedding y.val (D.rationalLinear g v.val)) := by
    rw [map_smul, LinearMap.smul_apply, D.rationalPeriodLinear_reference hg]
    rfl
  change (QuotientAddGroup.mk
    (((q : ℤ) ^ n • D.rationalPeriodLinear g x)
      ((D.pel.level : ℂ)⁻¹ • D.periodReferenceEmbedding x.val v.val)) :
      Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ⧸ D.periodLattice y.val) =
    c • QuotientAddGroup.mk ((D.pel.level : ℂ)⁻¹ • D.periodReferenceEmbedding y.val v.val)
  rw [hf]
  exact Period.Marking.fractional_lattice_congruence (D.periodLattice y.val) D.pel.level hN c _ _
    (D.periodReferenceEmbedding y.val w) ((D.periodLattice_mem y.val _).mpr ⟨w, hw, rfl⟩) hp

end

end OAI.RepresentationTheory.Theta.Geometric
