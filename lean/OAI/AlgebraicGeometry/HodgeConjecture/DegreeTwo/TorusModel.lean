import OAI.Geometry.ComplexTorus.BettiLattice
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Periods
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport

/-! # Torus Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions

noncomputable section

/-! The BettiLattice H¹ model derived from the native abelian variety and canonical periods. -/

open _root_.CategoryTheory
open scoped TensorProduct _root_.Manifold ContDiff

open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods
  LatticePeriod.Constructions.LatticeDual Periods.Constructions.HodgePeriods

/-- The actual exponential lattice defines the torus underlying the abelian variety. -/
def abelianTorus (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Geometry.ComplexTorus.BettiLattice.CM.Construction.Torus where
  V := Transport.Constructions.AbelianModel A
  lattice := AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A
  full := AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full hHolomorphicAlgebraicity A

/-- Canonical complexification of the rational lattice dual, through actual Betti H¹. -/
def periodComparison (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) :
    ComplexMultiplication.WeightOne.CM.Complexification (abelianTorus hHolomorphicAlgebraicity A).H1Q ≃ₗ[ℂ]
      ((abelianTorus hHolomorphicAlgebraicity A).LQ →ₗ[ℚ] ℂ) :=
  (LinearEquiv.baseChange ℚ ℂ _ _ (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm).trans
    ((Transport.Constructions.h1ComplexificationEquiv A.variety H).trans
      ((AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A).trans (LatticePeriod.Constructions.LatticeDual.characterRestrictionEquiv (K := ℂ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).symm))

/-- Evaluation on the actual lattice removes only the final restriction equivalence. -/
theorem periodComparison_lattice (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (abelianTorus hHolomorphicAlgebraicity A).H1Q) (ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    periodComparison hHolomorphicAlgebraicity A H x (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) =
      AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A (Transport.Constructions.h1ComplexificationEquiv A.variety H
        ((LinearEquiv.baseChange ℚ ℂ _ _ (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm) x)) ℓ := by
  have h := (LatticePeriod.Constructions.LatticeDual.characterRestrictionEquiv (K := ℂ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).apply_symm_apply
    (AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A (Transport.Constructions.h1ComplexificationEquiv A.variety H
      ((LinearEquiv.baseChange ℚ ℂ _ _ (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm) x)))
  exact DFunLike.congr_fun h ℓ

/-- The comparison has the canonical tensor evaluation normalization on the lattice. -/
theorem periodComparison_tmul_lattice (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (z : ℂ) (φ : (abelianTorus hHolomorphicAlgebraicity A).H1Q) (ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    periodComparison hHolomorphicAlgebraicity A H (z ⊗ₜ[ℚ] φ) (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) =
      z * (φ (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) : ℂ) := by
  rw [periodComparison_lattice]
  change AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
      (z ⊗ₜ[ℚ] (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm φ)) ℓ = _
  rw [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
  erw [(AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A).map_smul]
  change z * AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of A.variety.analyticSpace) 1
        ((AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm φ)) ℓ = _
  erw [AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods_rationalToComplex, LinearEquiv.apply_symm_apply]
  rfl

/-- The tensor normalization extends to the whole rational lattice span. -/
theorem periodComparison_tmul (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (z : ℂ) (φ : (abelianTorus hHolomorphicAlgebraicity A).H1Q) (v : (abelianTorus hHolomorphicAlgebraicity A).LQ) :
    periodComparison hHolomorphicAlgebraicity A H (z ⊗ₜ[ℚ] φ) v = z * (φ v : ℂ) := by
  have he : periodComparison hHolomorphicAlgebraicity A H (z ⊗ₜ[ℚ] φ) =
      z • (Algebra.linearMap ℚ ℂ).comp φ := by
    apply LatticePeriod.Constructions.LatticeDual.characterRestriction_injective (K := ℂ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    ext ℓ
    exact periodComparison_tmul_lattice hHolomorphicAlgebraicity A H z φ ℓ
  exact LinearMap.congr_fun he v

/-- The actual Hodge decomposition has BettiLattice's exact holomorphic-covector criterion. -/
theorem periodComparison_holomorphic (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hH : Transport.Constructions.IsCanonicalH1 A.variety H)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (abelianTorus hHolomorphicAlgebraicity A).H1Q) :
    x ∈ (Transport.Constructions.hodgeAlongEquiv H (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm).holomorphic ↔
      ∃ f : (abelianTorus hHolomorphicAlgebraicity A).V →ₗ[ℂ] ℂ,
        ∀ v : (abelianTorus hHolomorphicAlgebraicity A).LQ, periodComparison hHolomorphicAlgebraicity A H x v = f v := by
  change (LinearEquiv.baseChange ℚ ℂ _ _ (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm) x ∈ H.holomorphic ↔ _
  rw [hH.1]
  change Transport.Constructions.h1ComplexificationEquiv A.variety H
    ((LinearEquiv.baseChange ℚ ℂ _ _ (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm) x) ∈
      A.variety.pureBettiSubspace 1 0 ↔ _
  rw [Periods.Constructions.HodgePeriods.holomorphic_iff_complexLinear_periods hHolomorphicAlgebraicity A]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have he : periodComparison hHolomorphicAlgebraicity A H x =
        (f.restrictScalars ℚ).comp (LatticePeriod.Constructions.LatticeDual.RationalSpan (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).subtype := by
      apply LatticePeriod.Constructions.LatticeDual.characterRestriction_injective (K := ℂ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
      ext ℓ
      exact (periodComparison_lattice hHolomorphicAlgebraicity A H x ℓ).trans (hf ℓ)
    exact fun v => LinearMap.congr_fun he v
  · rintro ⟨f, hf⟩
    refine ⟨f, fun ℓ => ?_⟩
    exact (periodComparison_lattice hHolomorphicAlgebraicity A H x ℓ).symm.trans
      (hf (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ))

/-- The BettiLattice model is constructed from actual singular H¹ and its canonical Hodge pieces. -/
def abelianH1Model (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hH : Transport.Constructions.IsCanonicalH1 A.variety H) : Geometry.ComplexTorus.BettiLattice.CM.Construction.H1Model (abelianTorus hHolomorphicAlgebraicity A) where
  hodge := Transport.Constructions.hodgeAlongEquiv H (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A).symm
  comparison := periodComparison hHolomorphicAlgebraicity A H
  comparison_tmul := periodComparison_tmul hHolomorphicAlgebraicity A H
  holomorphic_iff := periodComparison_holomorphic hHolomorphicAlgebraicity A H hH

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions
