import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UniqueLinearLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass

/-! # Theta Lift Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaLiftKernel.Intrinsic

noncomputable section

/-! The full GeometricTheta uniqueness conclusion forces the algebraic theta lift
to preserve all linear relations seen on the period domain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
  (c : D.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)

def nativePeriodChartIndex :=
  Σ x : D.domain, {p : AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x.val) ⟶ D.pel.complexSpace //
    D.IsPeriodChartAt c x p}

def nativeThetaObservation : D.pel.OneFormsA →ₗ[ℂ]
    ((nativePeriodChartIndex D c → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) ×
      (∀ i : {i : Fin D.pel.componentCount // i ≠ j}, AbelianScheme.TateComparison.FormConstants.OneForms (D.componentComplex i))) :=
  (LinearMap.pi (fun t : nativePeriodChartIndex D c =>
    (RepresentationTheory.Theta.Geometric.DifferentialNaturality.formInPeriodCoordinates t.1.val t.2.val).comp (D.pel.albanesePullback hg))).prod
    (LinearMap.pi (fun i : {i : Fin D.pel.componentCount // i ≠ j} =>
      (AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i)).comp (D.pel.albanesePullback hg)))

def nativeThetaObservedInput : D.sphericalInputs →ₗ[ℂ]
    ((nativePeriodChartIndex D c → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) ×
      (∀ i : {i : Fin D.pel.componentCount // i ≠ j}, AbelianScheme.TateComparison.FormConstants.OneForms (D.componentComplex i))) :=
  (LinearMap.pi (fun t : nativePeriodChartIndex D c =>
    (LinearMap.proj t.1.val).comp (D.thetaUniversal.comp D.sphericalInputs.subtype))).prod 0

theorem canonicalTheta_observation
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (hΘ : D.IsCanonicalThetaLift hg j c Θ) :
    (nativeThetaObservation D hg j c).comp Θ = nativeThetaObservedInput D j c := by
  apply LinearMap.ext
  intro φ
  apply Prod.ext
  · funext t
    exact hΘ.2.1 φ t.1 t.2.val t.2.property
  · funext i
    exact hΘ.2.2 i.val i.property φ

theorem canonicalTheta_of_observation
    (hcharts : ∀ x : D.domain, ∃ p, D.IsPeriodChartAt c x p)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (h : (nativeThetaObservation D hg j c).comp Θ = nativeThetaObservedInput D j c) :
    D.IsCanonicalThetaLift hg j c Θ := by
  refine ⟨hcharts, ?_, ?_⟩
  · intro φ x p hp
    exact congrArg (fun y => y.1 (⟨x, p, hp⟩ : nativePeriodChartIndex D c)) (LinearMap.congr_fun h φ)
  · intro i hi φ
    exact congrArg (fun y => y.2 (⟨i, hi⟩ : {i : Fin D.pel.componentCount // i ≠ j}))
      (LinearMap.congr_fun h φ)

theorem canonicalTheta_lift_zero
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (hΘ : D.IsCanonicalThetaLift hg j c Θ)
    (hu : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j c Ψ → Ψ = Θ)
    (φ : D.sphericalInputs) (hφ : ∀ x : D.domain, D.thetaUniversal φ.val x.val = 0) : Θ φ = 0 := by
  have huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      (nativeThetaObservation D hg j c).comp Ψ = nativeThetaObservedInput D j c → Ψ = Θ := by
    intro Ψ hΨ
    exact hu Ψ (canonicalTheta_of_observation D hg j c hΘ.1 Ψ hΨ)
  have hk : LinearMap.ker (nativeThetaObservedInput D j c) ≤ LinearMap.ker Θ :=
    UniqueLinearLift.unique_linear_lift_kernel (k := ℂ) (X := D.sphericalInputs)
      (V := D.pel.OneFormsA)
      (U := (nativePeriodChartIndex D c → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) ×
        (∀ i : {i : Fin D.pel.componentCount // i ≠ j}, AbelianScheme.TateComparison.FormConstants.OneForms (D.componentComplex i)))
      (nativeThetaObservation D hg j c) Θ
      (nativeThetaObservedInput D j c) (canonicalTheta_observation D hg j c Θ hΘ) huniq
  apply hk
  apply Prod.ext
  · funext t
    exact hφ t.1
  · rfl

theorem canonicalTheta_lift_relation
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (hΘ : D.IsCanonicalThetaLift hg j c Θ)
    (hu : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j c Ψ → Ψ = Θ)
    (φ ψ : D.sphericalInputs) (ω : ℂ)
    (hrel : ∀ x : D.domain, D.thetaUniversal φ.val x.val = ω • D.thetaUniversal ψ.val x.val) :
    Θ φ = ω • Θ ψ := by
  have hz := canonicalTheta_lift_zero D hg j c Θ hΘ hu (φ - ω • ψ) (by
    intro x
    change D.thetaUniversal (φ.val - ω • ψ.val) x.val = 0
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, hrel x, sub_self])
  have he : Θ (φ - ω • ψ) = Θ φ - ω • Θ ψ := by
    exact (map_sub (f := Θ) φ (ω • ψ)).trans
      (congrArg (fun a : D.pel.OneFormsA => Θ φ - a) (Θ.map_smul ω ψ))
  exact sub_eq_zero.mp (he.symm.trans hz)

theorem canonicalTheta_class_relation
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (hΘ : D.IsCanonicalThetaLift hg j c Θ)
    (hu : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j c Ψ → Ψ = Θ)
    (φ ψ : D.sphericalInputs) (ω : ℂ)
    (hrel : ∀ x : D.domain, D.thetaUniversal φ.val x.val = ω • D.thetaUniversal ψ.val x.val) :
    Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ = ω • Intrinsic.ThetaClass.nativeThetaClass D hg Θ ψ := by
  change Intrinsic.ThetaClass.nativeKaehlerClass D hg (Θ φ) = _
  rw [canonicalTheta_lift_relation D hg j c Θ hΘ hu φ ψ ω hrel, map_smul]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaLiftKernel.Intrinsic
