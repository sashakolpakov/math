import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitLinearTopology

/-! # Prime Chart -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization

noncomputable section

/-! Split all coordinates at one finite prime from the remaining finite adeles. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {ι : Type*}

def fullPrimeProjection : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[ℚ] (ι → ℚ_[q]) where
  toFun x i := FiniteSchur.Realization.finitePadicProjection q (x i)
  map_add' x y := by
    funext i
    exact (FiniteSchur.Realization.finitePadicProjection q).map_add (x i) (y i)
  map_smul' a x := by
    funext i
    exact (FiniteSchur.Realization.finitePadicProjection q).toLinearMap.map_smul a (x i)

def fullPrimeInclusion : (ι → ℚ_[q]) →ₗ[ℚ] (ι → Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun x i := FiniteSchur.Realization.finitePadicInclusion q (x i)
  map_add' x y := by
    funext i
    exact (FiniteSchur.Realization.finitePadicInclusion q).map_add (x i) (y i)
  map_smul' a x := by
    funext i
    exact (FiniteSchur.Realization.finitePadicInclusion q).map_smul a (x i)

theorem fullPrimeProjection_inclusion (x : ι → ℚ_[q]) :
    fullPrimeProjection q (fullPrimeInclusion q x) = x := by
  funext i
  exact FiniteSchur.Realization.finitePadicProjection_inclusion q (x i)

theorem fullPrimeProjection_continuous : Continuous (fullPrimeProjection q (ι := ι)) := by
  apply continuous_pi
  intro i
  exact (FiniteSchur.Realization.finitePadicProjection_continuous q).comp (continuous_apply i)

theorem fullPrimeInclusion_continuous : Continuous (fullPrimeInclusion q (ι := ι)) := by
  apply continuous_pi
  intro i
  exact (FiniteSchur.Realization.finitePadicInclusion_continuous q).comp (continuous_apply i)

abbrev FullPrimeAwayPosition := LinearMap.ker (fullPrimeProjection q (ι := ι))

def fullPrimeSplit : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₗ[ℚ] (ι → ℚ_[q]) × FullPrimeAwayPosition q (ι := ι) :=
  SplitLinearTopology.Realization.splitLinearEquiv (fullPrimeProjection q) (fullPrimeInclusion q) (fullPrimeProjection_inclusion q)

def fullPrimeChart : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ (ι → ℚ_[q]) × FullPrimeAwayPosition q (ι := ι) :=
  SplitLinearTopology.Realization.splitLinearHomeomorph (fullPrimeProjection q) (fullPrimeInclusion q) (fullPrimeProjection_inclusion q)
    (fullPrimeProjection_continuous q) (fullPrimeInclusion_continuous q)

def fullPrimeAway : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[ℚ] FullPrimeAwayPosition q (ι := ι) :=
  (LinearMap.snd ℚ (ι → ℚ_[q]) (FullPrimeAwayPosition q (ι := ι))).comp (fullPrimeSplit q).toLinearMap

theorem fullPrimeAway_val (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (fullPrimeAway q x).val = x - fullPrimeInclusion q (fullPrimeProjection q x) := rfl

theorem fullPrime_decomposition (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    fullPrimeInclusion q (fullPrimeProjection q x) + (fullPrimeAway q x).val = x := by
  rw [fullPrimeAway_val]
  abel

theorem fullPrimeChart_fst (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (fullPrimeChart q x).1 = fullPrimeProjection q x := rfl

theorem fullPrimeChart_snd (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (fullPrimeChart q x).2 = fullPrimeAway q x := rfl

theorem fullPrimeChart_symm (x : ι → ℚ_[q]) (y : FullPrimeAwayPosition q) :
    (fullPrimeChart q).symm (x, y) = fullPrimeInclusion q x + y.val := rfl

theorem fullPrimeAway_inclusion (x : ι → ℚ_[q]) : fullPrimeAway q (fullPrimeInclusion q x) = 0 := by
  apply Subtype.ext
  rw [fullPrimeAway_val, fullPrimeProjection_inclusion, sub_self]
  rfl

theorem fullPrimeAway_kernel (y : FullPrimeAwayPosition q (ι := ι)) : fullPrimeAway q y.val = y := by
  apply Subtype.ext
  rw [fullPrimeAway_val, show fullPrimeProjection q y.val = 0 from y.property, map_zero, sub_zero]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization
