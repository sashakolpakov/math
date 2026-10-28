import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DifferentialRankTower
import Mathlib.RingTheory.Etale.Kaehler

/-! # Inseparable Degree Bound -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.InseparableDegreeBound.Construction

noncomputable section

section

/-! Quantitative inseparability bounds for the geometric p-torsion argument. -/

open KaehlerDifferential _root_.Module IntermediateField
open scoped TensorProduct IntermediateField

/-- In a finite extension of characteristic p, each independent differential
requires a factor of p in the inseparable degree. -/
theorem pow_finrank_kaehler_le_finInsepDegree
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    p ^ Module.finrank L Ω[L⁄K] ≤ Field.finInsepDegree K L := by
  have htop : p ^ Module.finrank (⊤ : IntermediateField K L) Ω[(⊤ : IntermediateField K L)⁄K] ≤
      Field.finInsepDegree K (⊤ : IntermediateField K L) := by
    apply induction_on_adjoin
      (fun E : IntermediateField K L =>
        p ^ Module.finrank E Ω[E⁄K] ≤ Field.finInsepDegree K E)
    · have : Algebra.FormallyEtale K (⊥ : IntermediateField K L) :=
        Algebra.FormallyEtale.of_equiv (botEquiv K L).symm
      simp only [Module.finrank_zero_of_subsingleton, pow_zero, finInsepDegree_bot, le_refl]
    · intro E x hE
      let M := E⟮x⟯
      let b : PowerBasis E M := adjoin.powerBasis (IsIntegral.of_finite E x)
      have : Module.Finite E M := b.finite
      have : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
      have hsimple := DifferentialRankTower.Construction.pow_finrank_kaehler_le_finInsepDegree_powerBasis E M b p
      have htower := Nat.pow_le_pow_right (Fact.out : p.Prime).pos
        (DifferentialRankTower.Construction.finrank_kaehler_le_tower K E M)
      rw [pow_add] at htower
      exact htower.trans ((Nat.mul_le_mul hE hsimple).trans_eq
        (Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K E M))
  let E := (⊤ : IntermediateField K L)
  let e : E ≃ₐ[E] L := AlgEquiv.ofBijective (Algebra.ofId E L)
    ⟨Subtype.val_injective, fun x => ⟨⟨x, by trivial⟩, rfl⟩⟩
  have : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_equiv e
  have hdim : Module.finrank L Ω[L⁄K] = Module.finrank E Ω[E⁄K] := by
    rw [← (tensorKaehlerEquivOfFormallyEtale K E L).finrank_eq, Module.finrank_baseChange]
  rw [hdim]
  exact htop.trans_eq (finInsepDegree_top (F := K) K L)

/-- If the total degree is p^(2g) and the differential dimension is g,
the separable degree is at most p^g. -/
theorem finSepDegree_le_pow_of_finrank_kaehler
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (p g : ℕ) [Fact p.Prime] [CharP K p]
    (hdegree : Module.finrank K L = p ^ (2 * g))
    (hdiff : Module.finrank L Ω[L⁄K] = g) :
    Field.finSepDegree K L ≤ p ^ g := by
  have h := pow_finrank_kaehler_le_finInsepDegree K L p
  rw [hdiff] at h
  have hmul := Nat.mul_le_mul_left (Field.finSepDegree K L) h
  rw [Field.finSepDegree_mul_finInsepDegree, hdegree, two_mul, pow_add] at hmul
  exact Nat.le_of_mul_le_mul_right hmul (pow_pos (Fact.out : p.Prime).pos g)

end

/-! Zero differentials force a large inseparable part of a finite map. -/

open KaehlerDifferential
open scoped TensorProduct

/-- If the differential of K → L over k vanishes, changing the base of
differentials from k to K leaves the differential module unchanged. -/
def kaehlerEquivOfMapZero
    (k K L : Type*) [CommRing k] [CommRing K] [CommRing L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (hzero : KaehlerDifferential.map k k K L = 0) :
    Ω[L⁄k] ≃ₗ[L] Ω[L⁄K] := by
  apply LinearEquiv.ofBijective (KaehlerDifferential.map k K L L)
  refine ⟨?_, map_surjective k K L⟩
  rw [← LinearMap.ker_eq_bot, ← range_mapBaseChange k K L]
  have hbase : mapBaseChange k K L = 0 := by
    apply LinearMap.ext
    intro z
    induction z with
    | tmul r d => simp only [mapBaseChange_tmul, hzero, LinearMap.zero_apply, smul_zero]
    | add z w hz hw => simp only [map_add, hz, hw, LinearMap.zero_apply, add_zero]
  rw [hbase, LinearMap.range_zero]

/-- The inseparability estimate in the form used for multiplication by p
on the function field of an abelian variety. -/
theorem finSepDegree_le_pow_of_zero_differential
    (k K L : Type*) [CommRing k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [Module.Finite K L] (p g : ℕ) [Fact p.Prime] [CharP K p]
    (hzero : KaehlerDifferential.map k k K L = 0)
    (hdegree : Module.finrank K L = p ^ (2 * g))
    (hdiff : Module.finrank L Ω[L⁄k] = g) :
    Field.finSepDegree K L ≤ p ^ g := by
  apply finSepDegree_le_pow_of_finrank_kaehler K L p g hdegree
  exact (kaehlerEquivOfMapZero k K L hzero).finrank_eq.symm.trans hdiff

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.InseparableDegreeBound.Construction
