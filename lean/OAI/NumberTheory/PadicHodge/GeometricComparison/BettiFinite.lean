import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicClasses
import OAI.Analysis.HodgeTheory.Decomposition.SmoothHarmonic

/-! # Betti Finite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Finite dimensionality of actual positive-degree Betti cohomology from the finite weak harmonic kernels. -/

namespace BettiFinite.BettiHodge

section Components

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace]
  (n : ℕ)

/-- Embed actual smooth harmonic families into the componentwise weak harmonic kernels. -/
def componentToWeakHarmonics : Analysis.HodgeTheory.Decomposition.ComponentHarmonicTypes.Constructions.ComponentHarmonics X n →ₗ[ℂ]
    (∀ C : irreducibleComponents X.carrier, Analysis.HodgeTheory.Decomposition.WeakHarmonics.Constructions.ProjectiveWeakHarmonics (X.componentVariety C) n) where
  toFun a C := ⟨Analysis.HodgeTheory.Decomposition.SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy (X.componentVariety C) n (a.val C),
    (Analysis.HodgeTheory.Decomposition.SmoothHarmonic.Constructions.projective_smooth_energy_mem_weakHarmonics_iff (X.componentVariety C) n _).mpr
      (congrFun a.property C)⟩
  map_add' a b := by
    funext C
    apply Subtype.ext
    exact (Analysis.HodgeTheory.Decomposition.SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy (X.componentVariety C) n).map_add _ _
  map_smul' z a := by
    funext C
    apply Subtype.ext
    exact (Analysis.HodgeTheory.Decomposition.SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy (X.componentVariety C) n).map_smul z _

theorem componentToWeakHarmonics_injective : Function.Injective (componentToWeakHarmonics X n) := by
  intro a b h
  apply Subtype.ext
  funext C
  apply Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2_injective (X.componentVariety C) (n + 1)
  exact congrArg (fun u => Analysis.HodgeTheory.Decomposition.EnergyDomain.Constructions.projectiveEnergyInclusion (X.componentVariety C) n (u C).val) h

theorem componentHarmonics_finiteDimensional : FiniteDimensional ℂ (Analysis.HodgeTheory.Decomposition.ComponentHarmonicTypes.Constructions.ComponentHarmonics X n) := by
  let : ∀ C : irreducibleComponents X.carrier,
      FiniteDimensional ℂ (Analysis.HodgeTheory.Decomposition.WeakHarmonics.Constructions.ProjectiveWeakHarmonics (X.componentVariety C) n) :=
    fun C => Analysis.HodgeTheory.Decomposition.WeakHarmonics.Constructions.projectiveWeakHarmonics_finiteDimensional (X.componentVariety C) n
  exact FiniteDimensional.of_injective (componentToWeakHarmonics X n)
    (componentToWeakHarmonics_injective X n)

end Components

theorem positiveBetti_finiteDimensional (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    FiniteDimensional ℂ (X.complexCohomology (n + 1)) := by
  let : ∀ C : irreducibleComponents X.carrier,
      MeasurableSpace (X.componentVariety C).analyticSpace :=
    fun C => borel (X.componentVariety C).analyticSpace
  let : ∀ C : irreducibleComponents X.carrier,
      BorelSpace (X.componentVariety C).analyticSpace := fun _ => ⟨rfl⟩
  let : FiniteDimensional ℂ (Analysis.HodgeTheory.Decomposition.ComponentHarmonicTypes.Constructions.ComponentHarmonics X n) := componentHarmonics_finiteDimensional X n
  exact Module.Finite.of_surjective (Analysis.HodgeTheory.Decomposition.ComponentHarmonicClasses.Constructions.componentHarmonicBettiEquiv X n).toLinearMap
    (Analysis.HodgeTheory.Decomposition.ComponentHarmonicClasses.Constructions.componentHarmonicBettiEquiv X n).surjective

end BettiFinite.BettiHodge

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.complexBetti_finiteDimensional (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    FiniteDimensional ℂ (A.ComplexBetti j) :=
  BettiFinite.BettiHodge.positiveBetti_finiteDimensional (A.smoothProjectiveFiber j P) 0

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
