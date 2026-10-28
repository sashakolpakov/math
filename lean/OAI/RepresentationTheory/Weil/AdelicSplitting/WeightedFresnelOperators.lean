import OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnel
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnelMatrices
import OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelOperators

/-! # Weighted Fresnel Operators -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnelOperators.Construction

noncomputable section

/-! The weighted Fresnel relation is an equality of actual local cover
elements, with a restricted family of Gaussian circle scalars. -/

open scoped Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnel.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)

def scalarQuadraticFamily (b : F) : Rational.Construction.RestrictedCover F N ψ :=
  QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc (WeightedFresnelMatrices.Construction.scalarSymmetricMatrix F N b)

def scalarLeviFamily (b : F) (hb : b ≠ 0) : Rational.Construction.RestrictedCover F N ψ :=
  RationalLevi.Construction.rationalLeviFamily F N ψ (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb)

theorem scalarQuadraticFamily_operator (b : F) (v : ArchimedeanAdeles.Construction.Places F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
      (scalarQuadraticFamily F N ψ hc hu b v) f).val =
      Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) (ArchimedeanAdeles.Construction.rationalScalar F v b • 1) f.val := by
  change (Oscillator.Construction.localOperator _ _ _ (QuadraticGenerators.Construction.quadraticAtPlace F N ψ hu hc v
    (QuadraticGenerators.Construction.localizeQuadratic F N (WeightedFresnelMatrices.Construction.scalarSymmetricMatrix F N b) v)) f).val = _
  rw [WeightedFresnelMatrices.Construction.localizeScalarSymmetricMatrix]
  rfl

theorem scalarLeviFamily_operator (b : F) (hb : b ≠ 0) (v : ArchimedeanAdeles.Construction.Places F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (scalarLeviFamily F N ψ b hb v) f).val =
      fun x => ((Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus (ArchimedeanAdeles.Construction.Completion F v) (ArchimedeanAdeles.Construction.rationalScalar F v b) : ℝ))⁻¹ : ℂ) ^ N *
        f.val ((ArchimedeanAdeles.Construction.rationalScalar F v b)⁻¹ • x) := by
  funext x
  have h := (RationalLevi.Construction.rationalLeviFamily_spec F N ψ (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb)).2 v f x
  rw [WeightedFresnelMatrices.Construction.localizeScalarLinearMatrix, ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix_factor, ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix_substitution] at h
  exact h

def weightedGaussianPowerCircle (b : F) (hb : b ≠ 0) (v : ArchimedeanAdeles.Construction.Places F) : Circle :=
  ⟨Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) (ArchimedeanAdeles.Construction.rationalScalar F v b) ^ N, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_pow]
    have hbn : ArchimedeanAdeles.Construction.rationalScalar F v b ≠ 0 := by simpa only [map_zero] using (ArchimedeanAdeles.Construction.rationalScalar F v).injective.ne hb
    have hγ := ((Local.Analytic.Construction.localField_analytic_normalization (LocalKernel.Construction.completion_nondiscrete F v)
      (Characters.Construction.localAdditiveCharacter F ψ v) (Characters.Construction.localAdditiveCharacter_continuous F ψ hc v)
        (Characters.Construction.localAdditiveCharacter_unitary F ψ hu v) (hn v) N).2.2.1 _ hbn).2.1
    rw [Local.FunctionsMetaplectic.Construction.gaussianIndex_norm _ _ _ hγ, one_pow]⟩

def weightedFresnelFirstWord (b : F) (a : Rational.Construction.RestrictedCover F N ψ) : Rational.Construction.RestrictedCover F N ψ :=
  a * scalarQuadraticFamily F N ψ hc hu b * a

def weightedFresnelSecondWord (b : F) (hb : b ≠ 0) (a : Rational.Construction.RestrictedCover F N ψ) : Rational.Construction.RestrictedCover F N ψ :=
  scalarQuadraticFamily F N ψ hc hu (-b⁻¹) * scalarLeviFamily F N ψ b hb * a * scalarQuadraticFamily F N ψ hc hu (-b⁻¹)

theorem weighted_fresnel_words_projection (b : F) (hb : b ≠ 0)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a) (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F N ψ v (weightedFresnelFirstWord F N ψ hc hu b a v) =
      Vacuum.Construction.projectionAt F N ψ v (weightedFresnelSecondWord F N ψ hc hu b hb a v) := by
  change Vacuum.Construction.projectionAt F N ψ v ((a v * scalarQuadraticFamily F N ψ hc hu b v) * a v) =
    Vacuum.Construction.projectionAt F N ψ v (((scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v * scalarLeviFamily F N ψ b hb v) * a v) *
      scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v)
  simp only [map_mul]
  have hp := (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc (WeightedFresnelMatrices.Construction.scalarSymmetricMatrix F N b)).1 v
  have hm := (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc (WeightedFresnelMatrices.Construction.scalarSymmetricMatrix F N (-b⁻¹))).1 v
  have hl := (RationalLevi.Construction.rationalLeviFamily_spec F N ψ (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb)).1 v
  change Vacuum.Construction.projectionAt F N ψ v (scalarQuadraticFamily F N ψ hc hu b v) = _ at hp
  change Vacuum.Construction.projectionAt F N ψ v (scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v) = _ at hm
  change Vacuum.Construction.projectionAt F N ψ v (scalarLeviFamily F N ψ b hb v) = _ at hl
  rw [ha.1 v, hp, hm, hl]
  simp only [← map_mul]
  exact congrArg (Vacuum.Construction.rationalSymplecticLocal F N v) (WeightedFresnelMatrices.Construction.weighted_fresnel_symplectic_relation F N b hb)

theorem weighted_fresnel_words_scalar (b : F) (hb : b ≠ 0)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a) (v : ArchimedeanAdeles.Construction.Places F) :
    weightedFresnelFirstWord F N ψ hc hu b a v =
      Vacuum.Construction.scalarAt F N ψ v (weightedGaussianPowerCircle F N ψ hc hu hn b hb v) *
        weightedFresnelSecondWord F N ψ hc hu b hb a v := by
  apply NormalizationLevi.Construction.localCover_ext
  · change Vacuum.Construction.projectionAt F N ψ v _ = Vacuum.Construction.projectionAt F N ψ v _
    rw [map_mul, show Vacuum.Construction.projectionAt F N ψ v (Vacuum.Construction.scalarAt F N ψ v _) = 1 from rfl, one_mul]
    exact weighted_fresnel_words_projection F N ψ hc hu b hb a ha v
  · intro f x
    let O := Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
    let c := ArchimedeanAdeles.Construction.rationalScalar F v b
    have hcn : c ≠ 0 := by simpa only [map_zero] using (ArchimedeanAdeles.Construction.rationalScalar F v).injective.ne hb
    have hcomp (u w : Vacuum.Construction.CoverAt F N ψ v) (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) : O (u * w) g = O u (O w g) := by
      rw [map_mul]
      rfl
    have hw (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) : (O (a v) g).val =
        Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v) (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) g.val :=
      funext (ha.2 v g)
    have hqp (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) : (O (scalarQuadraticFamily F N ψ hc hu b v) g).val =
        Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) (c • 1) g.val := scalarQuadraticFamily_operator F N ψ hc hu b v g
    have hqm (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) : (O (scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v) g).val =
        Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) ((-c⁻¹) • 1) g.val := by
      simpa only [map_neg, map_inv₀] using! scalarQuadraticFamily_operator F N ψ hc hu (-b⁻¹) v g
    have hl (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) : (O (scalarLeviFamily F N ψ b hb v) g).val =
        fun y => ((Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus (ArchimedeanAdeles.Construction.Completion F v) c : ℝ))⁻¹ : ℂ) ^ N * g.val (c⁻¹ • y) :=
      scalarLeviFamily_operator F N ψ b hb v g
    change (O ((a v * scalarQuadraticFamily F N ψ hc hu b v) * a v) f).val x =
      (O (Vacuum.Construction.scalarAt F N ψ v (weightedGaussianPowerCircle F N ψ hc hu hn b hb v) *
        (((scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v * scalarLeviFamily F N ψ b hb v) * a v) *
          scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v)) f).val x
    simp only [hcomp]
    change (O (a v) (O (scalarQuadraticFamily F N ψ hc hu b v) (O (a v) f))).val x =
      Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) c ^ N *
        (O (scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v) (O (scalarLeviFamily F N ψ b hb v)
          (O (a v) (O (scalarQuadraticFamily F N ψ hc hu (-b⁻¹) v) f)))).val x
    simp only [hw, hqp, hqm, hl, Local.FunctionsMetaplectic.Construction.quadraticOperator_apply]
    have h := WeightedFresnel.LocalAnalysis.localField_weighted_fresnel (LocalKernel.Construction.completion_nondiscrete F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
      (Characters.Construction.localAdditiveCharacter_continuous F ψ hc v) (Characters.Construction.localAdditiveCharacter_unitary F ψ hu v) (hn v) c hcn f x
    rw [h]
    ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnelOperators.Construction
