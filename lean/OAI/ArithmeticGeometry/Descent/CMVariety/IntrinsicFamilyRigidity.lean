import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodMatrixRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodCoordinateContinuity
import OAI.ArithmeticGeometry.Descent.CMVariety.LinearLiftDerivative

/-! # Intrinsic Family Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyRigidity.Abelian.IntrinsicPeriods

noncomputable section

/-!
CM rigidity for continuous actual native periods and derivatives.
Canonical Hodge structures, holomorphic frames, integral endomorphism
matrices, their local constancy, and equivariance of the resulting
algebraic isomorphisms are all derived by the imported proofs.

The remaining geometric task is to obtain these continuous marked
periods and native derivative coordinates from an actual arithmetic
abelian-scheme family. This file does not postulate that uniformization
or construction of a representing arithmetic moduli scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

variable {S Index : Type} [TopologicalSpace S] [Fintype Index]

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

/-- The actual derivatives of the retained algebraic endomorphisms,
together with the actual marked periods, force local CM rigidity. -/
theorem continuous_native_periods_and_derivatives_locally_rigid
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (s₀ : S)
    (hperiod : ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀)
    (hCM : (A s₀).HasCMH1) :
    ∃ (r : ℕ) (g : Fin r → ((A s₀).toOver ⟶ (A s₀).toOver)),
      (∀ i, IsMonHom (g i)) ∧
      ∀ k : ∀ s, Fin r → ((A s).toOver ⟶ (A s).toOver),
        (∀ s i, IsMonHom (k s i)) →
        (∀ i, k s₀ i = g i) →
        (∀ l j, ContinuousAt
          (fun s => e s
            (mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s))) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s)))
              (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k s l)) (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).toOver)
                (b s j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s)))) s₀) →
        ∀ᶠ s in 𝓝 s₀,
          EquivariantRigidity.Abelian.IntrinsicPeriods.HasMarkedEquivariantIso (A s₀) (A s) (b s₀) (b s) g (k s) := by
  obtain ⟨r, g, hg, hrigid⟩ :=
    PeriodMatrixRigidity.Abelian.IntrinsicPeriods.continuous_period_and_endomorphism_matrices_locally_rigid A b d e s₀ hperiod hCM
  refine ⟨r, g, hg, ?_⟩
  intro k hk hk₀ hderiv
  apply hrigid k hk hk₀
  intro l
  apply PeriodCoordinateContinuity.Abelian.IntrinsicPeriods.markedEndomorphism_continuous_of_lift_images A b d e (fun s => k s l)
    (fun s => hk s l) s₀
  · exact PeriodCoordinateContinuity.Abelian.IntrinsicPeriods.realPeriodInCoordinates_continuousAt A b d e s₀ hperiod
  · dsimp only
    let (s : S) : IsMonHom (k s l) := hk s l
    intro j
    convert hderiv l j using 1
    ext s
    rw [LinearLiftDerivative.Abelian.IntrinsicPeriods.algebraicLinearLift_eq_mfderiv]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyRigidity.Abelian.IntrinsicPeriods
