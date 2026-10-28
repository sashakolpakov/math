import OAI.RepresentationTheory.Hecke.ThetaNonvanishing
import OAI.RepresentationTheory.Hecke.ThetaCentral

/-! # Theta Occurrence -/

namespace OAI.RepresentationTheory.Hecke.ThetaOccurrence.CentralConstraintIntrinsic

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)

theorem canonicalTheta_occurs_betti_of_forms
    (hg : D.pel.HasIntegralModelGeometry)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (A : Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (rho : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rho h))
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (heH : eH = Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ)
    (y : (Θ.comp J).range) (hy : y ≠ 0)
    (heigen : ∀ h, D.activeFormsComplex rho eH h y.val = χ h • y.val) :
    ∃ v : ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D.pel,
      v ∈ (ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J).range ∧ v ≠ 0 ∧
      ∀ h, Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h v = χ h • v := by
  exact ThetaCentral.ConstraintIntrinsic.actualBettiRadial_occurs D hg P hq hIsogenyQuotient A hA coeff rho hrho eH heH Θ J χ y
    (ThetaNonvanishing.CentralConstraintIntrinsic.canonicalTheta_radial_class_ne_zero D hg Θ j X component cover hcover hΘ huniq J y hy) heigen

/-- The premise is occurrence for the original forms image representation. -/
def FormsCentralConclusion (hg : D.pel.HasIntegralModelGeometry) (A : Theta.Geometric.TateComparison.Action D.pel)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (ρ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range)
    (M : ℕ) (ω : ℂ) : Prop :=
  let fullA := AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff
  ∀ fullSide : Fin s → Bool,
    Betti.CentralConstraintIntrinsic.Conclusion D.pel fullA D.pel.reference.distinguished fullSide →
    (letI := Betti.CentralConstraintIntrinsic.rationalBetti_finite D.pel hg;
      CentralConstraint.Construction.CommutingInput (fun h => Betti.CentralConstraintIntrinsic.nativeFullAction D.pel fullA h)) →
    ∀ χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ,
      (⨅ h, (Betti.CentralConstraintIntrinsic.nativeFullAction D.pel fullA h).genEigenspace (χ h) ⊤) ≠ ⊥ →
      (∃ y : (Θ.comp J).range, y ≠ 0 ∧
        ∀ h, ρ h y = Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ h • y) →
      ThetaCentral.ConstraintIntrinsic.ActualCentralConstraint D.pel fullA fullSide M ω χ

theorem canonicalTheta_central_from_forms
    (hg : D.pel.HasIntegralModelGeometry)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (A : Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (rho : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rho h))
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (heH : eH = Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (ρ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range)
    (hρ : ∀ h y, (ρ h y).val = D.activeFormsComplex rho eH h y.val)
    (hfull : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hg hq hIsogenyQuotient (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff))
    (M : ℕ) (ω : ℂ)
    (hB : SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset
      (Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)) (ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J) M ω) :
    FormsCentralConclusion D hg A coeff Θ J ρ M ω := by
  intro side hCentralAction hCommuting χ hχ hforms
  obtain ⟨y, hy, heigen⟩ := hforms
  have hocc := canonicalTheta_occurs_betti_of_forms D hg P hq hIsogenyQuotient A hA coeff rho hrho eH heH
    Θ j X component cover hcover hΘ huniq J (Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ) y hy (by
      intro h
      exact (hρ h y).symm.trans (congrArg Subtype.val (heigen h)))
  exact ThetaCentral.ConstraintIntrinsic.actualCentralConclusion_of_satake D.pel hg hq hIsogenyQuotient _ hfull _ M ω hB
    side hCentralAction hCommuting χ hχ hocc

end

end OAI.RepresentationTheory.Hecke.ThetaOccurrence.CentralConstraintIntrinsic
