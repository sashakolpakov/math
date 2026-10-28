import OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension
import Mathlib.RingTheory.RamificationInertia.Inertia
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer

/-! # Divisor Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorDimension

noncomputable section

/-! A divisor point with nonzero residue degree retains codimension one
under a map between finite-type integral algebras of equal dimension.
This excludes exceptional divisors from ungraded point pushforward. -/

open _root_.Order

open OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension.Construction

theorem quotient_dimension_add_height_le (A : Type*) [CommRing A] (p : PrimeSpectrum A) :
    (p.asIdeal.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p.asIdeal) ≤ ringKrullDim A := by
  let : Nonempty (PrimeSpectrum A) := ⟨p⟩
  have hc : ringKrullDim (A ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, coheight_eq_krullDim_Ici]
    rfl
  rw [hc, PrimeSpectrum.height_eq_orderHeight, ← WithBot.coe_add]
  rw [ringKrullDim, krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun q : PrimeSpectrum A => height q + coheight q) p)

theorem height_eq_one_of_dimension_drop (K A : Type) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (p : Ideal A) [p.IsPrime]
    (h : (Algebra.trdeg K (A ⧸ p)).toNat + 1 = (Algebra.trdeg K A).toNat) : p.height = 1 := by
  have hb := quotient_dimension_add_height_le A ⟨p, inferInstance⟩
  rw [DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K A, DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K (A ⧸ p), ← h,
    Nat.cast_add, Nat.cast_one, add_comm _ (1 : WithBot ℕ∞)] at hb
  have hp : p.height ≤ 1 := WithBot.coe_le_coe.mp (ENat.WithBot.add_le_add_natCast_right_iff.mp hb)
  have hn : p ≠ ⊥ := by
    intro he
    rw [he, (AlgEquiv.quotientBot K A).trdeg_eq] at h
    omega
  exact le_antisymm hp (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hn))

theorem quotient_trdeg_eq_residue (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (p : Ideal A) [p.IsPrime] : Algebra.trdeg K (A ⧸ p) = Algebra.trdeg K p.ResidueField := by
  exact Foundations.Scheme.TranscendenceDegreeTransfer.trdeg_eq_of_isFractionRing K (A ⧸ p) p.ResidueField

theorem quotient_trdeg_eq_of_inertiaDeg_ne_zero
    (K A B : Type) [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (q : Ideal B) [q.IsPrime] (hq : q.inertiaDeg A ≠ 0) :
    Algebra.trdeg K (A ⧸ q.under A) = Algebra.trdeg K (B ⧸ q) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  let : IsScalarTower K (q.under A).ResidueField q.ResidueField :=
    IsScalarTower.to₁₃₄ K A (q.under A).ResidueField q.ResidueField
  have hpos : 0 < Module.finrank (q.under A).ResidueField q.ResidueField := by
    rw [← Ideal.inertiaDeg_def]
    exact Nat.pos_of_ne_zero hq
  let := Module.finite_of_finrank_pos hpos
  rw [quotient_trdeg_eq_residue, quotient_trdeg_eq_residue]
  have h := trdeg_add_eq K (q.under A).ResidueField (A := q.ResidueField)
  rwa [trdeg_eq_zero (R := (q.under A).ResidueField) (A := q.ResidueField), add_zero] at h

/-- A nonzero native residue degree prevents a divisor from changing
codimension between finite-type algebras of equal transcendence degree. -/
theorem height_under_eq_one (K A B : Type) [Field K] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra K A] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B] [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (hdim : (Algebra.trdeg K A).toNat = (Algebra.trdeg K B).toNat)
    (q : Ideal B) [q.IsPrime] (hq : q.height = 1) (hdeg : q.inertiaDeg A ≠ 0) :
    (q.under A).height = 1 := by
  apply height_eq_one_of_dimension_drop K A (q.under A)
  rw [quotient_trdeg_eq_of_inertiaDeg_ne_zero K A B q hdeg, hdim]
  exact DivisorClass.Chern.HeightOneDimension.Construction.finiteType_height_one_trdeg K B q hq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorDimension
