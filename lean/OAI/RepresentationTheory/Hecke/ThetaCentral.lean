import OAI.RepresentationTheory.Hecke.Intrinsic
import OAI.RepresentationTheory.Hecke.IntrinsicConclusion
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion

/-! # Theta Central -/

namespace OAI.RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic

noncomputable section

section

/-! Transport the same algebraic theta and radial inclusion to the actual
Betti space. No new theta witness or assumed compatibility equation is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)

/-- The actual integration class of the given theta forms on the given radial family. -/
def actualBettiRadial (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs) :
    SphericalActionModelInverse.Radial q →ₗ[ℂ] ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D.pel :=
  (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg).comp (Θ.comp J)

theorem actualBettiRadial_eq_nativeThetaClass (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs) :
    actualBettiRadial D hg Θ J = (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeThetaClass D hg Θ).comp J := rfl

theorem nativeActiveAction_eq (A : Theta.Geometric.TateComparison.Action D.pel)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ) :
    (Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)).toLinearMap =
      D.activeH1Complex A (Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished) := by
  apply LinearMap.ext
  intro h
  induction h using TensorProduct.inductionOn with
  | tmul z h => rfl
  | add h k hh hk =>
      simp only [map_add, hh, hk]
      exact ((D.activeH1Complex A
        (Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished)).map_add h k).symm

theorem actualBettiRadial_covariance
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
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (hcov : ∀ h b, Θ (J (SphericalActionModelInverse.radialAction q .inverseCoset h b)) =
      D.activeFormsComplex rho eH h (Θ (J b))) (h) (b) :
    actualBettiRadial D hg Θ J (SphericalActionModelInverse.radialAction q .inverseCoset h b) =
      Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h
        (actualBettiRadial D hg Θ J b) := by
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg (Θ (J _)) = _
  rw [hcov, ← AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass.Intrinsic.nativeKaehlerClass_active D hg P hq hIsogenyQuotient A hA rho hrho eH]
  subst eH
  exact (LinearMap.congr_fun (nativeActiveAction_eq D A coeff) h |> congrArg
    (fun f => f (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg (Θ (J b))))).symm

theorem actualBettiRadial_dilation (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (M : ℕ) (ω : ℂ)
    (hdil : ∀ b, Θ (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)) = ω • Θ (J b))
    (b) : actualBettiRadial D hg Θ J
      ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b) = ω • actualBettiRadial D hg Θ J b := by
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg (Θ (J _)) = _
  rw [hdil, map_smul]
  rfl

theorem actualBettiRadial_range (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs) :
    (actualBettiRadial D hg Θ J).range =
      (Θ.comp J).range.map (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg) := by
  exact LinearMap.range_comp _ _

/-- The canonical map between the two actual images is a quotient map. -/
def formsImageToBetti (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs) :
    (Θ.comp J).range →ₗ[ℂ] (actualBettiRadial D hg Θ J).range :=
  ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg).comp (Θ.comp J).range.subtype).codRestrict _ (by
    rintro ⟨y, b, hb⟩
    exact ⟨b, congrArg (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg) hb⟩)

theorem formsImageToBetti_surjective (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs) :
    Function.Surjective (formsImageToBetti D hg Θ J) := by
  rintro ⟨v, b, hb⟩
  exact ⟨(Θ.comp J).rangeRestrict b, Subtype.ext hb⟩

/-- Nonzero images of occurring forms give occurring Betti characters.
The nonzero condition concerns the actual class of this same vector. -/
theorem actualBettiRadial_occurs
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
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ)
    (y : (Θ.comp J).range) (hy : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg y.val ≠ 0)
    (heigen : ∀ h, D.activeFormsComplex rho eH h y.val = χ h • y.val) :
    ∃ v : ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D.pel,
      v ∈ (actualBettiRadial D hg Θ J).range ∧ v ≠ 0 ∧
      ∀ h, Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h v = χ h • v := by
  refine ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg y.val, ?_, hy, ?_⟩
  · obtain ⟨b, hb⟩ := y.property
    exact ⟨b, congrArg (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg) hb⟩
  · intro h
    subst eH
    have hact := LinearMap.congr_fun (nativeActiveAction_eq D A coeff) h
    change Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h = _ at hact
    have hnatural := AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass.Intrinsic.nativeKaehlerClass_active D hg P hq hIsogenyQuotient A hA rho hrho
      (Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished) h y.val
    rw [heigen, map_smul] at hnatural
    exact (congrArg (fun f => f (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg y.val)) hact).trans hnatural

theorem actualBettiRadial_satake
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
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : RadialDilation.Cm.algebraicUnitCircle ω)
    (hcov : ∀ h b, Θ (J (SphericalActionModelInverse.radialAction q .inverseCoset h b)) =
      D.activeFormsComplex rho eH h (Θ (J b)))
    (hdil : ∀ b, Θ (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)) = ω • Θ (J b)) :
    SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset
      (Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff))
      (actualBettiRadial D hg Θ J) M ω := by
  apply SphericalActionModelInverse.projective_satake_parameters_of_radial_quotient q .inverseCoset
    _ _ _ M hM ω (hω.2 ω (minpoly.aeval ℚ ω))
  · exact actualBettiRadial_covariance D hg P hq hIsogenyQuotient A hA coeff rho hrho eH heH Θ J hcov
  · exact actualBettiRadial_dilation D hg Θ J M ω hdil

end

/-! The exact preserved central constraint, specialized to the constructed
Betti radial map and the inverse-coset convention. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def ActualCentralConstraint (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (fullSide : Fin s → Bool)
    (M : ℕ) (ω : ℂ) (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ) : Prop :=
    let α := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ
    let C := (1 : ℂ) ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide
    let r := (Real.sqrt (q : ℝ) : ℂ)
    ∃ e₀ : ℂ, e₀ ≠ 0 ∧ e₀ ^ M = ω ∧
      let e := (SphericalActionModelInverse.parameterForConvention .inverseCoset e₀)⁻¹
      IsAlgebraic ℚ e ∧
      ∃ b : ℂ, ∃ σ : Equiv.Perm (Fin 3),
        b ≠ 0 ∧ IsAlgebraic ℚ b ∧ (∀ i, IsAlgebraic ℚ (α i)) ∧
        (∀ i, χ C * α i = b * (![r, r⁻¹, e] : Fin 3 → ℂ) (σ i)) ∧
        b ^ 3 * e = (χ C) ^ 3 * χ (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) ∧
        (∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1 ∧
          ∀ γ : ℂ ≃ₐ[ℚ] ℂ, ((γ b) ^ 3 * γ e) ^ n = 1) ∧
        χ (C * (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 1)) =
          (q : ℂ) * b * (r + r⁻¹ + e) ∧
        χ (C ^ 2 * (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 2)) =
          (q : ℂ) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e)

/-- Full CentralAction and Commuting are instantiated on this same native action. -/
def ActualCentralConclusion (hg : D.HasIntegralModelGeometry) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (B : SphericalActionModelInverse.Radial q →ₗ[ℂ] ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D)
    (M : ℕ) (ω : ℂ) : Prop :=
  ∀ (fullSide : Fin s → Bool),
    Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide →
    (letI := Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg;
      CentralConstraint.Construction.CommutingInput (fun h => Betti.CentralConstraintIntrinsic.nativeFullAction D A h)) →
    ∀ χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ,
      (⨅ h, (Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥ →
      (∃ v : ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D, v ∈ B.range ∧ v ≠ 0 ∧
        ∀ h, Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A h v = Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ h • v) →
      ActualCentralConstraint D A fullSide M ω χ

/-- A named conjunction keeps the large geometric output within Lean's
normal elaboration budget while exposing both complete conclusions. -/
def ActualBettiConclusion (hg : D.HasIntegralModelGeometry) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (B : SphericalActionModelInverse.Radial q →ₗ[ℂ] ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D)
    (M : ℕ) (ω : ℂ) : Prop :=
  SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset
    (V := ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D) (Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A) B M ω ∧
  ActualCentralConclusion D hg A B M ω

theorem actualCentralConclusion_of_satake (hg : D.HasIntegralModelGeometry)
    (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (B : SphericalActionModelInverse.Radial q →ₗ[ℂ] ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D)
    (M : ℕ) (ω : ℂ)
    (hB : SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset
      (Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A) B M ω) :
    ActualCentralConclusion D hg A B M ω := by
  intro side hCentralAction hCommuting χ hχ hBχ
  exact Intrinsic.CentralConstraintIntrinsic.native_central_constraint_on_full_satake_extensions D hg hq hIsogenyQuotient A hA
    side hCentralAction .inverseCoset B M ω hB hCommuting χ hχ hBχ

end

end OAI.RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic
