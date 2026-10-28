import OAI.RepresentationTheory.Hecke.ThetaCentral
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaLiftKernel

/-! # Theta Nonvanishing -/

namespace OAI.RepresentationTheory.Hecke.ThetaNonvanishing.CentralConstraintIntrinsic

noncomputable section

/-! The original nonzero-forms premise suffices on the actual canonical
theta range. Uniqueness detects a nonzero period covector, and exact
holomorphic one-form vanishing detects its nonzero Betti class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry)
  (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
  (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (component : X.toOver ≅ D.componentComplex j)
  (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
  (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
  (huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
    D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ)

include hcover hΘ huniq

theorem canonicalTheta_class_ne_zero_of_forms (φ : D.sphericalInputs) (hφ : Θ φ ≠ 0) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ ≠ 0 := by
  intro hz
  apply hφ
  apply AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaLiftKernel.Intrinsic.canonicalTheta_lift_zero D hg j (D.totalPeriodMap j X component cover) Θ hΘ huniq φ
  intro x
  apply ContinuousLinearMap.ext
  intro u
  change D.thetaUniversal φ.val x.val u = 0
  by_contra hvalue
  exact (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroClass.nativeThetaClass_ne_zero_of_period_value D hg Θ j X component cover hcover hΘ
    φ x u hvalue) hz

theorem canonicalTheta_class_eq_zero_iff (φ : D.sphericalInputs) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ = 0 ↔ Θ φ = 0 := by
  constructor
  · intro hz
    by_contra hφ
    exact canonicalTheta_class_ne_zero_of_forms D hg Θ j X component cover hcover hΘ huniq φ hφ hz
  · intro hz
    change AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg (Θ φ) = 0
    rw [hz, map_zero]

theorem canonicalTheta_radial_class_eq_zero_iff
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (y : (Θ.comp J).range) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg y.val = 0 ↔ y.val = 0 := by
  obtain ⟨b, hb⟩ := y.property
  have h := canonicalTheta_class_eq_zero_iff D hg Θ j X component cover hcover hΘ huniq (J b)
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg ((Θ.comp J) b) = 0 ↔ (Θ.comp J) b = 0 at h
  rw [hb] at h
  exact h

theorem canonicalTheta_radial_class_ne_zero
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (y : (Θ.comp J).range) (hy : y ≠ 0) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg y.val ≠ 0 := by
  intro hz
  exact hy (Subtype.ext ((canonicalTheta_radial_class_eq_zero_iff D hg Θ j X component
    cover hcover hΘ huniq J y).mp hz))

theorem canonicalTheta_formsImageToBetti_bijective
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs) :
    Function.Bijective (ThetaCentral.ConstraintIntrinsic.formsImageToBetti D hg Θ J) := by
  refine ⟨?_, ThetaCentral.ConstraintIntrinsic.formsImageToBetti_surjective D hg Θ J⟩
  intro y z hyz
  have hz : ThetaCentral.ConstraintIntrinsic.formsImageToBetti D hg Θ J (y - z) = 0 := by
    exact ((ThetaCentral.ConstraintIntrinsic.formsImageToBetti D hg Θ J).map_sub y z).trans (sub_eq_zero.mpr hyz)
  have hc : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg (y - z).val = 0 := congrArg Subtype.val hz
  have hf := (canonicalTheta_radial_class_eq_zero_iff D hg Θ j X component
    cover hcover hΘ huniq J (y - z)).mp hc
  exact sub_eq_zero.mp (Subtype.ext hf)

theorem canonicalTheta_actualBettiRadial_nonzero
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (hnz : ∃ b, Θ (J b) ≠ 0) : ∃ b, ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J b ≠ 0 := by
  obtain ⟨b, hb⟩ := hnz
  exact ⟨b, canonicalTheta_class_ne_zero_of_forms D hg Θ j X component cover hcover hΘ huniq
    (J b) hb⟩

end

end OAI.RepresentationTheory.Hecke.ThetaNonvanishing.CentralConstraintIntrinsic
