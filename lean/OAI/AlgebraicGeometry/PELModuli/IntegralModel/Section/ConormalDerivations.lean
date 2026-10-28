import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalMaps
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Conormal Derivations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal

noncomputable section

/-! Derivations at a smooth algebra section are the actual linear
functionals on its conormal, compatibly with every coefficient scalar. -/

open scoped TensorProduct

variable (R B K : Type) [CommRing R] [CommRing B] [CommRing K]
  [Algebra R B] [Algebra B R] [IsScalarTower R B R]
  [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsScalarTower B R K]
  [Algebra.FormallySmooth R B]

def derivationConormalEquivOverBase : Derivation R B K ≃ₗ[R]
    ((RingHom.ker (algebraMap B R)).Cotangent →ₗ[R] K) :=
  ((KaehlerDifferential.linearMapEquivDerivation R B).symm.restrictScalars R).trans
    ((LinearMap.liftBaseChangeEquiv R).trans
      (LinearEquiv.congrLeft K R (Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv R B).symm))

theorem derivationConormalEquivOverBase_toCotangent (d : Derivation R B K)
    (b : RingHom.ker (algebraMap B R)) :
    derivationConormalEquivOverBase R B K d (Ideal.toCotangent _ b) = d b := by
  change LinearMap.liftBaseChange R d.liftKaehlerDifferential
    (Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv R B (Ideal.toCotangent _ b)) = d b
  rw [Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv_toCotangent,
    LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]

def derivationConormalEquiv : Derivation R B K ≃ₗ[K]
    ((RingHom.ker (algebraMap B R)).Cotangent →ₗ[R] K) where
  toEquiv := (derivationConormalEquivOverBase R B K).toEquiv
  map_add' := (derivationConormalEquivOverBase R B K).map_add
  map_smul' c d := by
    apply LinearMap.ext
    intro v
    obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap B R)) v
    change derivationConormalEquivOverBase R B K (c • d) (Ideal.toCotangent _ b) =
      c • derivationConormalEquivOverBase R B K d (Ideal.toCotangent _ b)
    rw [derivationConormalEquivOverBase_toCotangent, derivationConormalEquivOverBase_toCotangent]
    rfl

theorem derivationConormalEquiv_toCotangent (d : Derivation R B K)
    (b : RingHom.ker (algebraMap B R)) :
    derivationConormalEquiv R B K d (Ideal.toCotangent _ b) = d b :=
  derivationConormalEquivOverBase_toCotangent R B K d b

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal
