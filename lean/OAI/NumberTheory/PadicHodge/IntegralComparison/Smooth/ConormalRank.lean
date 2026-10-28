import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Conormal Rank -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank

/-! The conormal rank of a smooth quotient is the difference of the two
relative differential ranks. The proof uses the actual split cotangent
sequence and works over an arbitrary coefficient ring. -/

open KaehlerDifferential
open scoped TensorProduct

variable {k Q : Type*} [CommRing k] [CommRing Q] [Algebra k Q]
  (P : Algebra.Extension k Q) [Algebra.Smooth k P.Ring] [Algebra.Smooth k Q]

def differentialSplit :
    P.CotangentSpace ≃ₗ[Q] P.Cotangent × Ω[Q⁄k] :=
  (P.exact_cotangentComplex_toKaehler.splitInjectiveEquiv P.toKaehler_surjective
    ⟨Classical.choose (P.formallySmooth_iff_split_injection.mp inferInstance),
      Classical.choose_spec (P.formallySmooth_iff_split_injection.mp inferInstance)⟩).1

theorem extension_rank [Module.Finite Q P.Cotangent] (p : PrimeSpectrum Q) :
    Module.rankAtStalk Ω[P.Ring⁄k] (p.comap (algebraMap P.Ring Q)) =
      Module.rankAtStalk P.Cotangent p + Module.rankAtStalk Ω[Q⁄k] p := by
  let : Module.Projective Q P.Cotangent := AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalDerivationLift.Construction.smooth_extension_conormal_projective P
  have h := congrFun (Module.rankAtStalk_eq_of_equiv (differentialSplit P)) p
  rw [Module.rankAtStalk_prod, Pi.add_apply] at h
  change Module.rankAtStalk (Q ⊗[P.Ring] Ω[P.Ring⁄k]) p = _ at h
  rw [Module.rankAtStalk_baseChange] at h
  exact h

variable {R : Type*} [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]

theorem quotient_rank (p : PrimeSpectrum (R ⧸ I)) :
    Module.rankAtStalk Ω[R⁄k] (p.comap (Ideal.Quotient.mk I)) =
      Module.rankAtStalk I.Cotangent p + Module.rankAtStalk Ω[R ⧸ I⁄k] p := by
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  let : Algebra.Smooth k P.Ring := inferInstanceAs (Algebra.Smooth k R)
  let e := AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I
  let : Module.Finite (R ⧸ I) I.Cotangent := AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.smooth_quotient_conormal_finite I
  let : Module.Finite (R ⧸ I) P.Cotangent := Module.Finite.equiv e.symm
  have h := extension_rank P p
  have he := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  exact h.trans (congrArg (fun n => n + Module.rankAtStalk Ω[R ⧸ I⁄k] p) he)

theorem quotient_rank_sub (p : PrimeSpectrum (R ⧸ I)) :
    Module.rankAtStalk I.Cotangent p =
      Module.rankAtStalk Ω[R⁄k] (p.comap (Ideal.Quotient.mk I)) -
        Module.rankAtStalk Ω[R ⧸ I⁄k] p := by
  rw [quotient_rank (k := k) I p, Nat.add_sub_cancel]

end NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank

namespace NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank.SplitNormalization

/-! The chosen smooth cotangent splitting retains the actual conormal
inclusion and the actual projection to quotient Kähler differentials. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (P : Algebra.Extension R S) [Algebra.Smooth R P.Ring] [Algebra.Smooth R S]

theorem maps :
    P.cotangentComplex = (differentialSplit P).symm.toLinearMap.comp
      (LinearMap.inl S P.Cotangent Ω[S⁄R]) ∧
    P.toKaehler = (LinearMap.snd S P.Cotangent Ω[S⁄R]).comp
      (differentialSplit P).toLinearMap :=
  (P.exact_cotangentComplex_toKaehler.splitInjectiveEquiv P.toKaehler_surjective
    ⟨Classical.choose (P.formallySmooth_iff_split_injection.mp inferInstance),
      Classical.choose_spec (P.formallySmooth_iff_split_injection.mp inferInstance)⟩).2

theorem inl (x : P.Cotangent) :
    (differentialSplit P).symm (x, 0) = P.cotangentComplex x :=
  (LinearMap.congr_fun (maps P).1 x).symm

theorem snd (x : P.CotangentSpace) :
    (differentialSplit P x).2 = P.toKaehler x :=
  (LinearMap.congr_fun (maps P).2 x).symm

end NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank.SplitNormalization

end

end OAI
