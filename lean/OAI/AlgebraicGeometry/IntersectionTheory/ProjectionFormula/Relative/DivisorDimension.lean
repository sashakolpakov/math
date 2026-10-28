import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorDimension
import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields

/-! # Divisor Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.DivisorDimension

noncomputable section

/-! Dimension-one fibers in finite-type integral algebras. Primes over
the generic point have height at most one, and a height-one prime with
nonzero residue degree can only map to the generic point. -/

open _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorDimension

theorem height_eq_zero_of_quotient_dimension_eq (K A : Type) [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (p : Ideal A) [p.IsPrime]
    (hd : (Algebra.trdeg K (A ⧸ p)).toNat = (Algebra.trdeg K A).toNat) : p.height = 0 := by
  have hb := Affine.DivisorDimension.quotient_dimension_add_height_le A ⟨p, inferInstance⟩
  rw [DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K A, DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K (A ⧸ p), hd] at hb
  have hb' : (p.height : WithBot ℕ∞) + ((Algebra.trdeg K A).toNat : WithBot ℕ∞) ≤
      (0 : WithBot ℕ∞) + ((Algebra.trdeg K A).toNat : WithBot ℕ∞) := by simpa using hb
  exact le_antisymm
    (WithBot.coe_le_coe.mp (ENat.WithBot.add_le_add_natCast_right_iff.mp hb')) bot_le

variable (K A B : Type) [Field K] [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B]
  (hdim : (Algebra.trdeg K A).toNat + 1 = (Algebra.trdeg K B).toNat)

include hdim

omit [IsDomain A] [Algebra.FiniteType K A] in
theorem height_le_one_over_bot (q : Ideal B) [q.IsPrime] (hq : q.under A = ⊥) :
    q.height ≤ 1 := by
  let φ : A →ₐ[K] B ⧸ q := (Ideal.Quotient.mkₐ K q).comp (IsScalarTower.toAlgHom K A B)
  have hi : Function.Injective φ := by
    apply (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mpr
    change RingHom.ker ((Ideal.Quotient.mk q).comp (algebraMap A B)) = ⊥
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact hq
  have ht := trdeg_le_of_injective φ hi
  let : Algebra.FiniteType K (B ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K q) Ideal.Quotient.mk_surjective
  have hc : (Algebra.trdeg K A).toNat ≤ (Algebra.trdeg K (B ⧸ q)).toNat :=
    Cardinal.toNat_le_toNat ht (trdeg_lt_aleph0_of_finiteType (R := K) (S := B ⧸ q))
  have hb := Affine.DivisorDimension.quotient_dimension_add_height_le B ⟨q, inferInstance⟩
  rw [DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K B, DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K (B ⧸ q),
    ← hdim, Nat.cast_add, Nat.cast_one, add_comm _ (1 : WithBot ℕ∞)] at hb
  have hb' : (q.height : WithBot ℕ∞) + ((Algebra.trdeg K A).toNat : WithBot ℕ∞) ≤
      (1 : WithBot ℕ∞) + ((Algebra.trdeg K A).toNat : WithBot ℕ∞) := by
    have hm : ((Algebra.trdeg K A).toNat : WithBot ℕ∞) ≤
        ((Algebra.trdeg K (B ⧸ q)).toNat : WithBot ℕ∞) := by exact_mod_cast hc
    calc
      _ ≤ (q.height : WithBot ℕ∞) + ((Algebra.trdeg K (B ⧸ q)).toNat : WithBot ℕ∞) :=
        add_le_add le_rfl hm
      _ ≤ _ := hb
  exact WithBot.coe_le_coe.mp (ENat.WithBot.add_le_add_natCast_right_iff.mp hb')

theorem under_eq_bot_of_height_one_of_degree (q : Ideal B) [q.IsPrime]
    (hq : q.height = 1) (hdeg : q.inertiaDeg A ≠ 0) : q.under A = ⊥ := by
  have hd : (Algebra.trdeg K (A ⧸ q.under A)).toNat = (Algebra.trdeg K A).toNat := by
    have ht := DivisorClass.Chern.HeightOneDimension.Construction.finiteType_height_one_trdeg K B q hq
    rw [← Affine.DivisorDimension.quotient_trdeg_eq_of_inertiaDeg_ne_zero K A B q hdeg] at ht
    omega
  exact Ideal.height_eq_zero_iff_eq_bot.mp (height_eq_zero_of_quotient_dimension_eq K A (q.under A) hd)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.DivisorDimension
