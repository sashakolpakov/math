import Mathlib.RingTheory.Smooth.Basic

/-! # Section Cotangent -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual conormal module of a smooth algebra section -/

open KaehlerDifferential TensorProduct

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B]

omit [Algebra.FormallySmooth A B] in
theorem algebraSection_surjective : Function.Surjective (algebraMap B A) := by
  intro a
  exact ⟨algebraMap A B a, (IsScalarTower.algebraMap_apply A B A a).symm⟩

theorem smoothSectionCotangent_injective : Function.Injective (kerCotangentToTensor A B A) :=
  (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := A) (A := A) (P := B)
    (algebraSection_surjective A B)).mpr inferInstance

omit [Algebra.FormallySmooth A B] in
theorem smoothSectionCotangent_surjective : Function.Surjective (kerCotangentToTensor A B A) := by
  intro x
  exact (exact_kerCotangentToTensor_mapBaseChange A B A (algebraSection_surjective A B) x).mp
    (Subsingleton.elim _ _)

def smoothSectionCotangentEquivOverAmbient :
    (RingHom.ker (algebraMap B A)).Cotangent ≃ₗ[B] A ⊗[B] Ω[B⁄A] :=
  LinearEquiv.ofBijective (kerCotangentToTensor A B A)
    ⟨smoothSectionCotangent_injective A B, smoothSectionCotangent_surjective A B⟩

def smoothSectionCotangentEquiv :
    (RingHom.ker (algebraMap B A)).Cotangent ≃ₗ[A] A ⊗[B] Ω[B⁄A] :=
  (smoothSectionCotangentEquivOverAmbient A B).restrictScalars A

theorem smoothSectionCotangentEquiv_toCotangent (x : RingHom.ker (algebraMap B A)) :
    smoothSectionCotangentEquiv A B (Ideal.toCotangent _ x) = 1 ⊗ₜ D A B x.1 := rfl

instance smoothSectionCotangent_projective : Module.Projective A (RingHom.ker (algebraMap B A)).Cotangent :=
  Module.Projective.of_equiv (smoothSectionCotangentEquiv A B).symm

instance smoothSectionCotangent_finite [IsNoetherianRing B] :
    Module.Finite A (RingHom.ker (algebraMap B A)).Cotangent := by
  have : Module.Finite B (RingHom.ker (algebraMap B A)).Cotangent :=
    Module.Finite.of_surjective (Ideal.toCotangent (RingHom.ker (algebraMap B A)))
      (Ideal.toCotangent_surjective _)
  have : Module.Finite B (A ⊗[B] Ω[B⁄A]) := Module.Finite.equiv (smoothSectionCotangentEquivOverAmbient A B)
  have : Module.Finite A (A ⊗[B] Ω[B⁄A]) := Module.Finite.of_restrictScalars_finite B A _
  exact Module.Finite.equiv (smoothSectionCotangentEquiv A B).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles
