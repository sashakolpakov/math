import OAI.RepresentationTheory.Hecke.Intrinsic

/-! # Intrinsic Parameters -/

namespace OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

noncomputable section

/-! Lift the native CentralConstraint character and its three absorbed Hecke values
through the chosen complex embedding. No scalar-matching hypothesis is used. -/

open scoped TensorProduct
open OAI.RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic

/-- The algebraic numbers in ℂ, used only to invert the chosen embedding. -/
abbrev algebraicField := algebraicClosure ℚ ℂ

def chosenClosureEquiv (j : AlgebraicClosure ℚ →+* ℂ) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] algebraicField := by
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  letI : IsAlgClosure ℚ algebraicField := algebraicClosure.isAlgClosure ℚ ℂ
  let f := j.toRatAlgHom.codRestrict algebraicField.toSubalgebra
    (fun a => mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom j.toRatAlgHom))
  exact AlgEquiv.ofBijective f
    (Algebra.IsAlgebraic.algHom_bijective₂ f
      (IsAlgClosure.equiv ℚ algebraicField (AlgebraicClosure ℚ)).toAlgHom).1

theorem chosenClosureEquiv_inverse (j : AlgebraicClosure ℚ →+* ℂ) (a : algebraicField) :
    j ((chosenClosureEquiv j).symm a) = (a : ℂ) :=
  congrArg (fun a : algebraicField => (a : ℂ)) ((chosenClosureEquiv j).apply_symm_apply a)

def liftComplexAlgebraic (j : AlgebraicClosure ℚ →+* ℂ) (z : ℂ) (hz : IsAlgebraic ℚ z) :
    AlgebraicClosure ℚ := (chosenClosureEquiv j).symm ⟨z, hz.isIntegral⟩

theorem liftComplexAlgebraic_image (j : AlgebraicClosure ℚ →+* ℂ) (z : ℂ)
    (hz : IsAlgebraic ℚ z) : j (liftComplexAlgebraic j z hz) = z :=
  chosenClosureEquiv_inverse j _

theorem complexSqrt_sq (q : ℕ) : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
  norm_cast
  exact Real.sq_sqrt (Nat.cast_nonneg _)

def algebraicSqrt (q : ℕ) (j : AlgebraicClosure ℚ →+* ℂ) : AlgebraicClosure ℚ :=
  liftComplexAlgebraic j (Real.sqrt (q : ℝ) : ℂ)
    (IsAlgebraic.of_pow (n := 2) (by decide)
      ((complexSqrt_sq q).symm ▸ isAlgebraic_natCast q))

theorem algebraicSqrt_image (q : ℕ) (j : AlgebraicClosure ℚ →+* ℂ) :
    j (algebraicSqrt q j) = (Real.sqrt (q : ℝ) : ℂ) := liftComplexAlgebraic_image j _ _

theorem algebraicSqrt_sq (q : ℕ) (j : AlgebraicClosure ℚ →+* ℂ) :
    (algebraicSqrt q j) ^ 2 = (q : AlgebraicClosure ℚ) :=
  j.injective (by rw [map_pow, algebraicSqrt_image, complexSqrt_sq, map_natCast])

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def absorbedHecke (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (fullSide : Fin s → Bool) : Fin 3 → AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q :=
  let C := AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide
  ![C * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1,
    C ^ 2 * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2,
    C ^ 3 * AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished]

def algebraicNativeCharacter (hg : D.HasIntegralModelGeometry) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (j : AlgebraicClosure ℚ →+* ℂ)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥) :
    AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] AlgebraicClosure ℚ :=
  (chosenClosureEquiv j).symm.toAlgHom.comp
    (((χ.restrictScalars ℚ).comp Algebra.TensorProduct.includeRight).codRestrict
      algebraicField.toSubalgebra (fun h => mem_algebraicClosure_iff.mpr
        (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.native_rational_eigenvalues_algebraic D hg A χ hχ h)))

@[simp] theorem algebraicNativeCharacter_image (hg : D.HasIntegralModelGeometry) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (j : AlgebraicClosure ℚ →+* ℂ)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :
    j (algebraicNativeCharacter D hg A j χ hχ h) = χ (1 ⊗ₜ[ℚ] h) :=
  chosenClosureEquiv_inverse j _

def satakeValues {F : Type*} [Field F] (q : ℕ) (r b e : F) : Fin 3 → F :=
  ![(q : F) * b * (r + r⁻¹ + e),
    (q : F) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e), b ^ 3 * e]

theorem satakeValues_map {F G : Type*} [Field F] [Field G]
    (j : F →+* G) (q : ℕ) (r b e : F) (i : Fin 3) :
    j (satakeValues q r b e i) = satakeValues q (j r) (j b) (j e) i := by
  fin_cases i <;> simp [satakeValues]

/-- The three identities are consequences of native CentralConstraint on the actual
TateComparison character. The dilation root and inverse-coset convention are retained. -/
theorem parameters_from_native_CentralConstraint
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (fullSide : Fin s → Bool)
    (hCentralAction : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide)
    (c : RepresentationTheory.Hecke.SphericalActionModelInverse.ActingConvention)
    (Θ : RepresentationTheory.Hecke.SphericalActionModelInverse.Radial q →ₗ[ℂ] ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D)
    (M : ℕ) (ω : ℂ)
    (hSphericalAction : RepresentationTheory.Hecke.SphericalActionModelInverse.RadialSatakeConclusion q c
      (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A) Θ M ω)
    (hCommuting : letI := RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg
      RepresentationTheory.Hecke.CentralConstraint.Construction.CommutingInput (fun h => RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h))
    (j : AlgebraicClosure ℚ →+* ℂ)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hΘχ : ∃ v : ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D, v ∈ LinearMap.range Θ ∧ v ≠ 0 ∧
      ∀ h, RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A h v = RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ h • v) :
    ∃ e₀ : ℂ, e₀ ≠ 0 ∧ e₀ ^ M = ω ∧
      ∃ r b e : AlgebraicClosure ℚ,
        r ^ 2 = (q : AlgebraicClosure ℚ) ∧
        j r = (Real.sqrt (q : ℝ) : ℂ) ∧ b ≠ 0 ∧
        j e = (RepresentationTheory.Hecke.SphericalActionModelInverse.parameterForConvention c e₀)⁻¹ ∧
        (∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1) ∧
        ∀ i, algebraicNativeCharacter D hg A j χ hχ (absorbedHecke D A fullSide i) =
          satakeValues q r b e i := by
  obtain ⟨e₀, he₀, hroot, healg, bc, _σ, hb, hbalg, _hαalg, _hproj,
    hcentral, ⟨n, hn, hpow, _hconj⟩, h₁, h₂⟩ :=
    RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.native_central_constraint_on_full_satake_extensions D hg hq hIsogenyQuotient A hTateComparison
      fullSide hCentralAction c Θ M ω hSphericalAction hCommuting χ hχ hΘχ
  let ec := (RepresentationTheory.Hecke.SphericalActionModelInverse.parameterForConvention c e₀)⁻¹
  let r := algebraicSqrt q j
  let b := liftComplexAlgebraic j bc hbalg
  let e := liftComplexAlgebraic j ec healg
  have hr : j r = (Real.sqrt (q : ℝ) : ℂ) := algebraicSqrt_image q j
  have hbimg : j b = bc := liftComplexAlgebraic_image j bc hbalg
  have heimg : j e = ec := liftComplexAlgebraic_image j ec healg
  let χrat := (χ.restrictScalars ℚ).comp Algebra.TensorProduct.includeRight
  have hmul (h k : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) : χ (1 ⊗ₜ[ℚ] (h * k)) =
      χ (1 ⊗ₜ[ℚ] h) * χ (1 ⊗ₜ[ℚ] k) := map_mul χrat h k
  have hpowrat (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (m : ℕ) : χ (1 ⊗ₜ[ℚ] (h ^ m)) =
      χ (1 ⊗ₜ[ℚ] h) ^ m := map_pow χrat h m
  refine ⟨e₀, he₀, hroot, r, b, e, algebraicSqrt_sq q j, hr,
    (fun hz => hb (by simpa only [hz, map_zero] using hbimg.symm)), heimg,
    ⟨n, hn, j.injective ?_⟩, ?_⟩
  · simp only [map_pow, map_mul, map_one, hbimg, heimg]
    exact hpow
  · intro i
    apply j.injective
    rw [algebraicNativeCharacter_image, satakeValues_map, hr, hbimg, heimg]
    fin_cases i
    · change χ (1 ⊗ₜ[ℚ] (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide *
        AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1)) =
          (q : ℂ) * bc * ((Real.sqrt (q : ℝ) : ℂ) + (Real.sqrt (q : ℝ) : ℂ)⁻¹ + ec)
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using h₁
    · change χ (1 ⊗ₜ[ℚ] (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide ^ 2 *
        AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2)) =
          (q : ℂ) * bc ^ 2 * ((Real.sqrt (q : ℝ) : ℂ) * (Real.sqrt (q : ℝ) : ℂ)⁻¹ +
            (Real.sqrt (q : ℝ) : ℂ) * ec + (Real.sqrt (q : ℝ) : ℂ)⁻¹ * ec)
      simpa only [Algebra.TensorProduct.tmul_pow, one_pow,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul] using h₂
    · change χ (1 ⊗ₜ[ℚ] (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide ^ 3 *
        AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished)) = bc ^ 3 * ec
      rw [hmul, hpowrat]
      exact hcentral.symm

theorem norm_of_dilation_root {c : RepresentationTheory.Hecke.SphericalActionModelInverse.ActingConvention}
    {e₀ : ℂ} (h : RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle e₀) :
    ‖(RepresentationTheory.Hecke.SphericalActionModelInverse.parameterForConvention c e₀)⁻¹‖ = 1 := by
  have he : ‖e₀‖ = 1 := h.2 e₀ (minpoly.aeval ℚ e₀)
  cases c <;> simp [RepresentationTheory.Hecke.SphericalActionModelInverse.parameterForConvention, he]

end

end OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
