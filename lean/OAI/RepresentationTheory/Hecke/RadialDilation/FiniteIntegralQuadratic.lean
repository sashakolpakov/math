import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticLift
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteFourierVacuum

/-! # Finite Integral Quadratic -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteIntegralQuadratic.Realization

noncomputable section

/-! Integral quadratic coefficients give finite-adelic lattice-vector stabilization. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HalfIntegralMatrix (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) : Prop :=
  ∀ i j, algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j ∈ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele

omit [Fintype ι] [DecidableEq ι] in
theorem HalfIntegralMatrix.neg {B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf} (hB : HalfIntegralMatrix B) :
    HalfIntegralMatrix (-B) := by
  intro i j
  change algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * (-B i j) ∈ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele
  rw [mul_neg]
  exact Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem (hB i j)

omit [DecidableEq ι] in
theorem halfIntegral_quadratic_mem (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : HalfIntegralMatrix B)
    (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (hx : x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) : QuadraticCommutator.Realization.ringQuadratic B x ∈ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  rw [QuadraticCommutator.Realization.ringQuadratic_entries]
  apply Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem
  intro i _
  apply Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem
  intro j _
  exact Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (hx i) (hB i j)) (hx j)

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finiteQuadratic_integral_vacuum (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : HalfIntegralMatrix B) :
    FiniteQuadratic.Realization.finiteQuadratic D B Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  apply Subtype.ext
  funext x
  change D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) * Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x = Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x
  by_cases hx : x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors
  · rw [Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_integral D _ (halfIntegral_quadratic_mem B hB x hx), one_mul]
  · rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_notMem hx, mul_zero]

theorem every_finite_integral_upper_sign (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (hBi : HalfIntegralMatrix B)
    (m : MpF) (hm : D.finite.project m = QuadraticCommutator.Realization.ringUpper B hB) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ε • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  obtain ⟨ε, hε, ha⟩ := FiniteQuadraticLift.Realization.every_finite_quadratic_lift D B hB m hm
  refine ⟨ε, hε, ?_⟩
  rw [ha, finiteQuadratic_integral_vacuum D B hBi]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteIntegralQuadratic.Realization
