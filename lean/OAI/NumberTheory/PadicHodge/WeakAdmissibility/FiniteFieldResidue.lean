import OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittUnramified
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField

/-! # Finite Field Residue -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue

noncomputable section

/-! The actual valuation ring and finite residue field of a finite p-adic subextension. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Scalars
variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

instance fieldValued : Valued K NNReal := NormedField.toValued

abbrev FieldIntegers := Valued.integer K
abbrev FieldResidue := IsLocalRing.ResidueField (FieldIntegers p K)

instance fieldRankOne : Valuation.RankOne (Valued.v : Valuation K NNReal) :=
  inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := K)))

def integerToCp : FieldIntegers p K →+* 𝓞_ℂ_[p] where
  toFun a := ⟨algebraMap (PadicAlgCl p) ℂ_[p] (a.val : PadicAlgCl p), by
    change Valued.v (algebraMap (PadicAlgCl p) ℂ_[p] (a.val : PadicAlgCl p)) ≤ 1
    rw [Logarithm.PeriodRings.valuation_eq_nnnorm]
    have h := a.property
    change ‖(a.val : K)‖₊ ≤ 1 at h
    exact (PadicComplex.nnnorm_extends p (a.val : PadicAlgCl p)).le.trans h⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem integerToCp_norm (a : FieldIntegers p K) :
    ‖(integerToCp p K a : ℂ_[p])‖ = ‖(a : K)‖ :=
  PadicComplex.norm_extends p (a.val : PadicAlgCl p)

instance integerToCp_local : IsLocalHom (integerToCp p K) := by
  apply ((IsLocalRing.local_hom_TFAE (integerToCp p K)).out 4 1 rfl rfl).mp
  intro a ha
  change integerToCp p K a ∈ IsLocalRing.maximalIdeal 𝓞_ℂ_[p]
  erw [Valuation.mem_maximalIdeal_iff] at ha ⊢
  change ‖(a : K)‖₊ < 1 at ha
  rw [Logarithm.PeriodRings.valuation_eq_nnnorm]
  exact_mod_cast (integerToCp_norm p K a).trans_lt (show ‖(a : K)‖ < 1 from ha)

def residueEmbedding : FieldResidue p K →+* PrimitiveElements.ResidueCp p :=
  IsLocalRing.ResidueField.map (integerToCp p K)

theorem residueEmbedding_residue (a : FieldIntegers p K) :
    residueEmbedding p K (IsLocalRing.residue (FieldIntegers p K) a) =
      IsLocalRing.residue 𝓞_ℂ_[p] (integerToCp p K a) :=
  IsLocalRing.ResidueField.map_residue _ a

instance fieldResidue_charP : CharP (FieldResidue p K) p :=
  (CharP.charP_iff_prime_eq_zero (R := FieldResidue p K) (Fact.out : p.Prime)).mpr (by
    apply (residueEmbedding p K).injective
    rw [map_natCast, map_zero, CharP.cast_eq_zero])

variable [Module.Finite ℚ_[p] K]

instance fieldIntegersCompact : CompactSpace (FieldIntegers p K) := by
  let : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  apply isCompact_iff_compactSpace.mp
  change IsCompact {x : K | ‖x‖ ≤ 1}
  simpa only [Metric.closedBall, dist_zero_right] using (isCompact_closedBall (0 : K) 1)

instance fieldIntegersDVR : IsDiscreteValuationRing (FieldIntegers p K) :=
  Valued.integer.isDiscreteValuationRing_of_compactSpace

instance fieldResidueFinite : Finite (FieldResidue p K) :=
  (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (show CompactSpace (FieldIntegers p K) from inferInstance)).2.2

instance fieldResidueFintype : Fintype (FieldResidue p K) := Fintype.ofFinite _

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue
