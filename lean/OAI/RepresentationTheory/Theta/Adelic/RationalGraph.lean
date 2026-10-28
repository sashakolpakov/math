import OAI.RepresentationTheory.Theta.Adelic.RationalFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalGraphPositive

/-! # Rational Graph -/

namespace OAI.RepresentationTheory.Theta.Adelic.RationalGraph

noncomputable section

/-! The canonical rational oscillator homomorphism is constructed from the
arithmetic character and exact Fourier family, before unitary local data. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.RationalGraphPositive.Construction
open OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial OAI.RepresentationTheory.Theta.Adelic.LocalFourier

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
variable (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)

include hc hu hn hp

theorem localProjection_kernel_circle (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F N ψ v)
    (ha : Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ v a = 1) : ∃ z : Circle, Weil.AdelicSplitting.Vacuum.Construction.scalarAt F N ψ v z = a :=
  Weil.AdelicSplitting.LocalKernel.Construction.localCover_kernel_circle (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu v)
    (FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp v) a ha

theorem globalProjection_kernel_circle (w : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N ψ)
    (ha : Weil.AdelicSplitting.Vacuum.Construction.globalProjection F N ψ a = 1) : ∃ z : Circle, Weil.AdelicSplitting.GlobalKernel.Construction.globalScalar F N ψ w z = a := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
    (Weil.AdelicSplitting.CentralProduct.Construction.scalarKernel (Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F N ψ) (Weil.AdelicSplitting.Vacuum.Construction.scalarAt F N ψ)) a
  have hproj (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ v (b v) = 1 :=
    congrArg (fun x : Weil.AdelicSplitting.Vacuum.Construction.AdelicSymplectic F N => x v) ha
  choose z hz using fun v => localProjection_kernel_circle F N ψ hc hu hn hp v (b v) (hproj v)
  exact Weil.AdelicSplitting.GlobalKernel.Construction.assemble_restricted_scalar F N ψ w b z (fun v => (hz v).symm)

theorem rationalGraph_identity_fiber (a : Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N ψ)
    (ha : (1, a) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ) : a = 1 := by
  let w : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F := .inl (Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace F)))
  have hpos := Weil.AdelicSplitting.RationalGraphPositive.Construction.rationalGraph_positive F N ψ hc hu hp
    (fun v => FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp (.inl v))
    (LocalFourier.local_positionMeasure_isAddHaarMeasure F ψ hc hu hn hp N) ha
  have hproj := Weil.AdelicSplitting.Rational.Construction.rationalGraph_covers F N ψ ha
  change Weil.AdelicSplitting.Vacuum.Construction.globalProjection F N ψ a = Weil.AdelicSplitting.Vacuum.Construction.rationalSymplectic F N 1 at hproj
  rw [map_one] at hproj
  exact Weil.AdelicSplitting.PositiveScalarProduct.Construction.globalPositiveTheta_scalar_eq_one F N ψ w a hpos
    (globalProjection_kernel_circle F N ψ hc hu hn hp w a hproj)

theorem rationalGraph_realization :
    ∃ r : Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N →* Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N ψ,
      (∀ γ a, (γ, a) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ ↔ r γ = a) ∧
      ∀ γ, Weil.AdelicSplitting.Vacuum.Construction.globalProjection F N ψ (r γ) = Weil.AdelicSplitting.Vacuum.Construction.rationalSymplectic F N γ :=
  Weil.AdelicSplitting.GraphReduction.Construction.rationalGraph_realization_of_total_and_identity_fiber F N ψ
    (Weil.AdelicSplitting.GraphReduction.Construction.rationalGraph_total_of_fourier_family F N ψ hu hc
      ⟨RationalFourier.rationalFourierFamily F ψ hc hu hn hp N,
        RationalFourier.rationalFourierFamily_spec F ψ hc hu hn hp N⟩)
    (rationalGraph_identity_fiber F N ψ hc hu hn hp)

end

end OAI.RepresentationTheory.Theta.Adelic.RationalGraph
