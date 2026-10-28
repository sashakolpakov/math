import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalFresnel
import OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelAlgebra
import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators

/-! # Fresnel Operators -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelOperators.Construction

noncomputable section

/-! The ratio of the two actual restricted Fourier-quadratic words is
the local Gaussian circle scalar at every place. -/

open scoped Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.LocalFresnel.Analysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)

def unitQuadraticFamily : Rational.Construction.RestrictedCover F N ψ :=
  QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc (FresnelAlgebra.Construction.unitSymmetricMatrix F N)

def negativeUnitQuadraticFamily : Rational.Construction.RestrictedCover F N ψ :=
  QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc (FresnelAlgebra.Construction.negativeUnitSymmetricMatrix F N)

theorem unitQuadraticFamily_operator (v : ArchimedeanAdeles.Construction.Places F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
      (unitQuadraticFamily F N ψ hc hu v) f).val = Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) 1 f.val := by
  have he : QuadraticGenerators.Construction.localizeQuadratic F N (FresnelAlgebra.Construction.unitSymmetricMatrix F N) v = FresnelAlgebra.Construction.unitSymmetricMatrix (ArchimedeanAdeles.Construction.Completion F v) N := by
    apply Subtype.ext
    exact (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix.map_one
  change (Oscillator.Construction.localOperator _ _ _ (QuadraticGenerators.Construction.quadraticAtPlace F N ψ hu hc v (QuadraticGenerators.Construction.localizeQuadratic F N (FresnelAlgebra.Construction.unitSymmetricMatrix F N) v)) f).val = _
  rw [he]
  rfl

theorem negativeUnitQuadraticFamily_operator (v : ArchimedeanAdeles.Construction.Places F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
      (negativeUnitQuadraticFamily F N ψ hc hu v) f).val = Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) (-1) f.val := by
  have he : QuadraticGenerators.Construction.localizeQuadratic F N (FresnelAlgebra.Construction.negativeUnitSymmetricMatrix F N) v = FresnelAlgebra.Construction.negativeUnitSymmetricMatrix (ArchimedeanAdeles.Construction.Completion F v) N := by
    apply Subtype.ext
    change (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix (-1) = -1
    rw [map_neg, map_one]
  change (Oscillator.Construction.localOperator _ _ _ (QuadraticGenerators.Construction.quadraticAtPlace F N ψ hu hc v (QuadraticGenerators.Construction.localizeQuadratic F N (FresnelAlgebra.Construction.negativeUnitSymmetricMatrix F N) v)) f).val = _
  rw [he]
  rfl

def gaussianPowerCircle (v : ArchimedeanAdeles.Construction.Places F) : Circle :=
  ⟨Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) 1 ^ N, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_pow, LocalFresnel.Construction.completion_gaussianIndex_one_norm F N ψ hc hu hn v, one_pow]⟩

def fresnelFirstWord (a : Rational.Construction.RestrictedCover F N ψ) : Rational.Construction.RestrictedCover F N ψ :=
  a * unitQuadraticFamily F N ψ hc hu * a

def fresnelSecondWord (a : Rational.Construction.RestrictedCover F N ψ) : Rational.Construction.RestrictedCover F N ψ :=
  negativeUnitQuadraticFamily F N ψ hc hu * a * negativeUnitQuadraticFamily F N ψ hc hu

theorem fresnel_words_projection (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F N ψ v (fresnelFirstWord F N ψ hc hu a v) =
      Vacuum.Construction.projectionAt F N ψ v (fresnelSecondWord F N ψ hc hu a v) := by
  change Vacuum.Construction.projectionAt F N ψ v ((a v * unitQuadraticFamily F N ψ hc hu v) * a v) =
    Vacuum.Construction.projectionAt F N ψ v ((negativeUnitQuadraticFamily F N ψ hc hu v * a v) * negativeUnitQuadraticFamily F N ψ hc hu v)
  simp only [map_mul]
  rw [ha.1 v]
  have hp := (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc (FresnelAlgebra.Construction.unitSymmetricMatrix F N)).1 v
  have hm := (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc (FresnelAlgebra.Construction.negativeUnitSymmetricMatrix F N)).1 v
  change Vacuum.Construction.projectionAt F N ψ v (unitQuadraticFamily F N ψ hc hu v) = _ at hp
  change Vacuum.Construction.projectionAt F N ψ v (negativeUnitQuadraticFamily F N ψ hc hu v) = _ at hm
  rw [hp, hm, ← map_mul, ← map_mul, ← map_mul, ← map_mul, FresnelAlgebra.Construction.fresnel_symplectic_relation]

theorem fresnel_words_scalar (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (v : ArchimedeanAdeles.Construction.Places F) :
    fresnelFirstWord F N ψ hc hu a v = Vacuum.Construction.scalarAt F N ψ v (gaussianPowerCircle F N ψ hc hu hn v) *
      fresnelSecondWord F N ψ hc hu a v := by
  apply NormalizationLevi.Construction.localCover_ext
  · change Vacuum.Construction.projectionAt F N ψ v _ = Vacuum.Construction.projectionAt F N ψ v _
    rw [map_mul, show Vacuum.Construction.projectionAt F N ψ v (Vacuum.Construction.scalarAt F N ψ v _) = 1 from rfl, one_mul]
    exact fresnel_words_projection F N ψ hc hu a ha v
  · intro f x
    let O := Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
    have hcomp (b c : Vacuum.Construction.CoverAt F N ψ v) (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
        O (b * c) g = O b (O c g) := by rw [map_mul]; rfl
    have hw (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) : (O (a v) g).val =
        Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v)
          (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) g.val := funext (ha.2 v g)
    have hqp (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
        (O (unitQuadraticFamily F N ψ hc hu v) g).val = Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) 1 g.val :=
      unitQuadraticFamily_operator F N ψ hc hu v g
    have hqm (g : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
        (O (negativeUnitQuadraticFamily F N ψ hc hu v) g).val = Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) (-1) g.val :=
      negativeUnitQuadraticFamily_operator F N ψ hc hu v g
    change (O ((a v * unitQuadraticFamily F N ψ hc hu v) * a v) f).val x =
      (O (Vacuum.Construction.scalarAt F N ψ v (gaussianPowerCircle F N ψ hc hu hn v) *
        ((negativeUnitQuadraticFamily F N ψ hc hu v * a v) * negativeUnitQuadraticFamily F N ψ hc hu v)) f).val x
    simp only [hcomp]
    change (O (a v) (O (unitQuadraticFamily F N ψ hc hu v) (O (a v) f))).val x =
      (Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) 1 ^ N) *
        (O (negativeUnitQuadraticFamily F N ψ hc hu v) (O (a v) (O (negativeUnitQuadraticFamily F N ψ hc hu v) f))).val x
    simp only [hw, hqp, hqm]
    rw [Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, Local.FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc]
    exact LocalFresnel.Construction.completion_fresnel F N ψ hc hu hn v f x

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelOperators.Construction
