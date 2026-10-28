import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalDerivationLift

/-! # Conormal Projective -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction

noncomputable section

/-! Finite projectivity of the actual conormal module of a smooth quotient ideal. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

def quotientExtensionCotangentEquiv (I : Ideal R) :
    (Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective).Cotangent ≃ₗ[R ⧸ I]
      I.Cotangent := by
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  let : Algebra R P.Ring := Algebra.id R
  let e₀ : P.Cotangent ≃ₗ[R] P.ker.Cotangent := P.cotangentEquivCotangentKer
  let e : P.Cotangent ≃ₗ[R] I.Cotangent :=
    e₀.trans (Ideal.Cotangent.equivOfEq _ I (Ideal.mk_ker : RingHom.ker (Ideal.Quotient.mk I) = I))
  exact e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

theorem smooth_quotient_conormal_projective [Algebra.FormallySmooth k R]
    (I : Ideal R) [Algebra.FormallySmooth k (R ⧸ I)] : Module.Projective (R ⧸ I) I.Cotangent := by
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  let : Algebra.FormallySmooth k P.Ring := inferInstanceAs (Algebra.FormallySmooth k R)
  let : Module.Projective (R ⧸ I) P.Cotangent := Smooth.ConormalDerivationLift.Construction.smooth_extension_conormal_projective P
  exact Module.Projective.of_equiv (quotientExtensionCotangentEquiv (k := k) I)

theorem smooth_quotient_conormal_finite [IsNoetherianRing R] (I : Ideal R) :
    Module.Finite (R ⧸ I) I.Cotangent := by
  let : Module.Finite R I.Cotangent := Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction
