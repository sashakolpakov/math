import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicKernel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicSourceOneForms

/-! # Source Intrinsic Kernel Factorization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicKernelFactorization.CM

noncomputable section

/-! Use the full native ThetaKernel conclusion to factor its actual total theta
form into actual source theta covectors. The supplied total finite input
is unchanged; each factor has one fixed returned source input. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem native_wedge_smul_pair (c₀ c₁ : ℂ)
    (a b : RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.Cotangent) :
    RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge (c₀ • a) (c₁ • b) = (c₀ * c₁) • RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge a b := by
  rw [RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge, RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedgeCoefficient_smul_left, RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedgeCoefficient_smul_right,
    RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge, smul_smul]
  congr 1
  ring

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true)
  (D : SourceIntrinsicKernel.CM.SourceNativeThetaKernelData K Q hμ)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

include hL in
theorem source_native_c38_factorization
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) 6) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ (n : ℕ) (φ ψ : Fin n → RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)),
      ∀ z : B.Domain, RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.thetaTopForm D.total.comparison f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) =
        ∑ i, c • RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge (Projection.CM.sourceThetaCovector K (L 0) (φ i) z.val)
          (Projection.CM.sourceThetaCovector K (L 1) (ψ i) z.val) := by
  obtain ⟨c, _, _, _, _, _, hcommon⟩ := D.conclusion
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hforms⟩ :=
    hcommon {f} ⊤ 1 Nat.one_pos
  obtain ⟨_, _, n, a, b, _, _, _, hw⟩ := (hforms f (Finset.mem_singleton_self f)).1
  let z₀ := SourceIntrinsicBall.CM.nativeSourceBallPoint K B RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic.origin
  let hC₀ := D.first_valid.2.2.2.2.1
  let hG₀ := D.first_valid.2.2.2.2.2.1
  let hC₁ := D.second_valid.2.2.2.2.1
  let hG₁ := D.second_valid.2.2.2.2.2.1
  let c₀ := IntrinsicSourceOneForms.CM.nativeSourceOneFormConstant K d Q hμ 0 D.first.comparison hC₀ (L 0) (hL 0) z₀
  let c₁ := IntrinsicSourceOneForms.CM.nativeSourceOneFormConstant K d Q hμ 1 D.second.comparison hC₁ (L 1) (hL 1) z₀
  let φ := fun i => SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ 0 D.first.comparison hC₀ (L 0) (hL 0) (a i)
  let ψ := fun i => SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ 1 D.second.comparison hC₁ (L 1) (hL 1) (b i)
  have hc₀ : c₀ ≠ 0 := IntrinsicSourceOneForms.CM.native_source_one_form_constant_ne_zero K d Q hμ 0
    D.first.comparison hC₀ hG₀ (L 0) (hL 0) z₀
  have hc₁ : c₁ ≠ 0 := IntrinsicSourceOneForms.CM.native_source_one_form_constant_ne_zero K d Q hμ 1
    D.second.comparison hC₁ hG₁ (L 1) (hL 1) z₀
  refine ⟨(c : ℂ) * (c₀ * c₁), mul_ne_zero (Units.ne_zero _) (mul_ne_zero hc₀ hc₁), n, φ, ψ, ?_⟩
  intro z
  refine (hw (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).trans (Finset.sum_congr rfl (fun i _ => ?_))
  have h₀ := IntrinsicSourceOneForms.CM.native_source_one_form K d Q hμ 0 D.first.comparison hC₀ hG₀ (L 0) (hL 0) (a i) z₀ z
  have h₁ := IntrinsicSourceOneForms.CM.native_source_one_form K d Q hμ 1 D.second.comparison hC₁ hG₁ (L 1) (hL 1) (b i) z₀ z
  have he := congrArg (fun w : RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.TopCovector => (c : ℂ) • w) (congrArg₂ RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge h₀ h₁)
  refine he.trans ?_
  rw [native_wedge_smul_pair, smul_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicKernelFactorization.CM
