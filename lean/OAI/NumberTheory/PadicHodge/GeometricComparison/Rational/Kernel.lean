import OAI.NumberTheory.PadicHodge.GeometricComparison.EpiCompact
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerGenerator
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CoefficientExactness

/-! # Kernel -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.Kernel.RationalProEtaleCoefficients

noncomputable section

/-! The kernel of actual integral-to-rational degree-one cohomology consists of classes killed by a power of ℓ. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry Opposite

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X]

theorem cokernel_integer_hom_torsion
    (a : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X ⟶ cokernel (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)) :
    ∃ N : ℕ, (ℓ ^ N) • a = 0 := by
  let π := cokernel.π (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)
  obtain ⟨U, g, hU, hg, s, hs⟩ := EpiCompact.EpiCompactLift.exists_lift π a
  let : IsAffine U.left := hU
  let : Surjective g.left := hg
  obtain ⟨N, t, ht⟩ := CoefficientExactness.RationalProEtaleCoefficients.sections_denominator ℓ X U s
  refine ⟨N, IntegerGenerator.IntegerGeneratorDetection.hom_eq_zero_of_cover g ((ℓ ^ N) • a) ?_⟩
  change (ℓ ^ N) • (a.hom.app (op U) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U)) = 0
  rw [← hs, ← map_nsmul, ← ht]
  exact congrArg
    (fun k : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X ⟶ cokernel (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) =>
      k.hom.app (op U) t) (cokernel.condition (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X))

theorem cokernelH0_torsion (x : (cokernel (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)).H 0) :
    ∃ N : ℕ, (ℓ ^ N) • x = 0 := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  obtain ⟨N, hN⟩ := cokernel_integer_hom_torsion ℓ X a
  refine ⟨N, ?_⟩
  have h := map_nsmul (Ext.addEquiv₀.symm :
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X ⟶ cokernel (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)) ≃+
      (cokernel (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)).H 0) (ℓ ^ N) a
  change Ext.mk₀ ((ℓ ^ N) • a) = (ℓ ^ N) • Ext.mk₀ a at h
  rw [← h, hN, Ext.mk₀_zero]

theorem integralH1_kernel_torsion (x : X.EllAdicCohomology ℓ 1)
    (hx : Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) 1 x = 0) :
    ∃ N : ℕ, (ℓ ^ N) • x = 0 := by
  let hS := CoefficientExactness.RationalProEtaleCoefficients.coefficientSequence_shortExact ℓ X
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) hS x hx rfl
  obtain ⟨N, hN⟩ := cokernelH0_torsion ℓ X y
  let δ := hS.extClass.postcomp (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) (zero_add 1)
  have hδ : δ y = x := hy
  refine ⟨N, ?_⟩
  have h := (map_nsmul δ (ℓ ^ N) y).symm.trans ((congrArg δ hN).trans δ.map_zero)
  exact (congrArg (fun z : X.EllAdicCohomology ℓ 1 => (ℓ ^ N) • z) hδ.symm).trans h

theorem cohomologyInclusion_kernel_torsion (x : X.EllAdicCohomology ℓ 1)
    (hx : ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X 1 x = 0) : ∃ N : ℕ, (ℓ ^ N) • x = 0 := by
  apply integralH1_kernel_torsion ℓ X x
  have h := congrArg (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X 1) hx
  change (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X 1)
    ((ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X 1).symm (Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) 1 x)) = _ at h
  simpa only [AddEquiv.apply_symm_apply, map_zero] using h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.Kernel.RationalProEtaleCoefficients
