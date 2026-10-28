import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars
import OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexResidueP

/-! # Residue Embedding -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueEmbedding

noncomputable section

/-!
# The actual residue-field embedding for a finite p-adic extension

The chosen algebraic-closure embedding preserves the canonical valuation.
It restricts to a local map of integer rings, hence to a residue-field
embedding. The local absolute Galois group fixes its image.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexResidueP

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

def complexEmbedding : K →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (CrystallineScalars.fieldEmbedding p K)

theorem complexEmbedding_valuation (x : K) :
    Valued.v (complexEmbedding p K x) = IntegralGeometry.fieldValuation p K x := by
  change Valued.v ((CrystallineScalars.fieldEmbedding p K x : PadicAlgCl p) : ℂ_[p]) = _
  rw [PadicComplex.valuation_extends]
  apply NNReal.eq
  change spectralNorm ℚ_[p] (PadicAlgCl p) (CrystallineScalars.fieldEmbedding p K x) = spectralNorm ℚ_[p] K x
  exact congrArg spectralValue (minpoly.algHom_eq (CrystallineScalars.fieldEmbedding p K) (CrystallineScalars.fieldEmbedding p K).injective x)

def integerEmbedding : IntegralGeometry.ringOfIntegers p K →+* 𝓞_ℂ_[p] where
  toFun x := ⟨complexEmbedding p K x, by
    change Valued.v (complexEmbedding p K x) ≤ 1
    rw [complexEmbedding_valuation]
    exact x.property⟩
  map_zero' := Subtype.ext (map_zero (complexEmbedding p K))
  map_one' := Subtype.ext (map_one (complexEmbedding p K))
  map_add' x y := Subtype.ext (map_add (complexEmbedding p K) (x : K) y)
  map_mul' x y := Subtype.ext (map_mul (complexEmbedding p K) (x : K) y)

instance integerEmbedding_local : IsLocalHom (integerEmbedding p K) where
  map_nonunit x hx := by
    apply ((Valuation.integer.integers (IntegralGeometry.fieldValuation p K)).isUnit_iff_valuation_eq_one).mpr
    have hv := (PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.mp hx
    change Valued.v (complexEmbedding p K x) = 1 at hv
    exact (complexEmbedding_valuation p K x).symm.trans hv

def residueEmbedding : IntegralGeometry.ResidueField p K →+* ComplexResidueP.ComplexResidue p :=
  IsLocalRing.ResidueField.map (integerEmbedding p K)

theorem residueEmbedding_residue (x : IntegralGeometry.ringOfIntegers p K) :
    residueEmbedding p K (IsLocalRing.residue (IntegralGeometry.ringOfIntegers p K) x) =
      IsLocalRing.residue 𝓞_ℂ_[p] (integerEmbedding p K x) :=
  IsLocalRing.ResidueField.map_residue (integerEmbedding p K) x

theorem residueEmbedding_injective : Function.Injective (residueEmbedding p K) :=
  (residueEmbedding p K).injective

theorem complexEmbedding_galois (σ : CrystallineScalars.LocalGalois K) (x : K) :
    PeriodRing.galoisComplexEquiv p (CrystallineScalars.galoisToPadic p K σ) (complexEmbedding p K x) = complexEmbedding p K x := by
  change UniformSpace.Completion.mapRingHom (CrystallineScalars.galoisToPadic p K σ).toRingHom
    (PeriodRing.algebraicGalois_isometry p (CrystallineScalars.galoisToPadic p K σ)).continuous
      ((CrystallineScalars.fieldEmbedding p K x : PadicAlgCl p) : ℂ_[p]) = (CrystallineScalars.fieldEmbedding p K x : PadicAlgCl p)
  exact (UniformSpace.Completion.mapRingHom_coe
    (PeriodRing.algebraicGalois_isometry p (CrystallineScalars.galoisToPadic p K σ)).continuous (CrystallineScalars.fieldEmbedding p K x)).trans
      (congrArg (algebraMap (PadicAlgCl p) ℂ_[p])
        (CrystallineScalars.conjugateRestriction_fixes_base ℚ_[p] (CrystallineScalars.closureEquiv p K) σ x))

theorem integerEmbedding_galois (σ : CrystallineScalars.LocalGalois K) (x : IntegralGeometry.ringOfIntegers p K) :
    PeriodRing.galoisIntegerEquiv p (CrystallineScalars.galoisToPadic p K σ) (integerEmbedding p K x) = integerEmbedding p K x :=
  Subtype.ext (complexEmbedding_galois p K σ x)

theorem residueEmbedding_galois (σ : CrystallineScalars.LocalGalois K) (x : IntegralGeometry.ResidueField p K) :
    IsLocalRing.ResidueField.map (PeriodRing.galoisIntegerEquiv p (CrystallineScalars.galoisToPadic p K σ)).toRingHom
      (residueEmbedding p K x) = residueEmbedding p K x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rw [residueEmbedding_residue, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue 𝓞_ℂ_[p]) (integerEmbedding_galois p K σ a)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueEmbedding
