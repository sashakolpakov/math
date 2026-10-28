import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedQuotientExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalAdjunction

/-! # Localized Conormal Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalResidue

noncomputable section

/-! The conormal residue for an actual smooth quotient commutes with
localization. The target bases are the genuine localized ideal classes
and Kähler differentials, and the ambient map is the native differential
base-change map. -/

open _root_.Module _root_.Algebra.Extension KaehlerDifferential
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedQuotientExtension

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (r : A) [IsLocalization.Away r B] (I : Ideal A)

local instance baseTower : IsScalarTower k (A ⧸ I) (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) :=
  AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I

local instance presentationAlgebra :
    Algebra (LocalizedQuotientExtension.presentation (k := k) I).Ring (LocalizedQuotientExtension.presentation (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I)).Ring :=
  inferInstanceAs (Algebra A B)

def ambient :
    (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) ⊗[A ⧸ I] ((A ⧸ I) ⊗[A] Ω[A⁄k])
      ≃ₗ[B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I] (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) ⊗[B] Ω[B⁄k] :=
  Etale.ConormalBaseChange.ambient
    (LocalizedQuotientExtension.presentation (k := k) I) (LocalizedQuotientExtension.presentation (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I))
    (LocalizedQuotientExtension.map I) (LocalizedQuotientExtension.formallyEtale I r)

theorem ambient_tmul_D (t : B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) (s : A ⧸ I) (a : A) :
    ambient (k := k) r I (t ⊗ₜ[A ⧸ I] (s ⊗ₜ[A] D k A a)) =
      (t * algebraMap (A ⧸ I) (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) s) ⊗ₜ[B]
        D k B (algebraMap A B a) :=
  Etale.ConormalBaseChange.ambient_tmul_D
    (LocalizedQuotientExtension.presentation (k := k) I) (LocalizedQuotientExtension.presentation (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I))
    (LocalizedQuotientExtension.map I) (LocalizedQuotientExtension.formallyEtale I r) t s a

variable [Algebra.Smooth k A] [Algebra.Smooth k (A ⧸ I)]
  [Algebra.Smooth k B] [Algebra.Smooth k (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I)]

local instance sourceSmooth : Algebra.Smooth k (LocalizedQuotientExtension.presentation (k := k) I).Ring :=
  inferInstanceAs (Algebra.Smooth k A)

local instance targetSmooth :
    Algebra.Smooth k (LocalizedQuotientExtension.presentation (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I)).Ring :=
  inferInstanceAs (Algebra.Smooth k B)

variable {c g : ℕ} (bI : Basis (Fin c) (A ⧸ I) I.Cotangent)
  (bQ : Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k])

omit [Algebra.Smooth k A] [Algebra.Smooth k (A ⧸ I)] [Algebra.Smooth k B] [Algebra.Smooth k (B ⧸ LocalizedQuotientExtension.extendedIdeal I)] in
theorem conormalBasis_eq :
    Etale.ConormalResidue.conormalBasis
      (LocalizedQuotientExtension.presentation (k := k) I) (LocalizedQuotientExtension.presentation (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I))
      (LocalizedQuotientExtension.map I) rfl (LocalizedQuotientExtension.kernel_bijective I r)
      (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) =
    (LocalizedConormalBases.conormalBasis (B := B) r I bI).map
      (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I)).symm := by
  apply DFunLike.ext
  intro i
  apply (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I)).injective
  rw [Etale.ConormalResidue.conormalBasis, Basis.map_apply, Basis.baseChange_apply,
    Etale.ConormalResidue.conormal_tmul, one_smul, LocalizedQuotientExtension.idealEquiv_map,
    Basis.map_apply, LinearEquiv.apply_symm_apply, Basis.map_apply,
    LinearEquiv.apply_symm_apply, LocalizedConormalBases.conormalBasis_apply]

theorem residue_naturality :
    (ConormalAdjunction.equivalence (LocalizedQuotientExtension.extendedIdeal (B := B) I)
      (LocalizedConormalBases.conormalBasis r I bI)
      (LocalizedConormalBases.quotientBasis r I bQ)).toLinearMap.comp
        ((exteriorPower.map (c + g) (ambient (k := k) r I).toLinearMap).comp
          (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap (A ⧸ I)
            (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) ((A ⧸ I) ⊗[A] Ω[A⁄k]) (c + g))) =
      ((exteriorPower.map g (LocalizedConormalBases.quotientEquiv (k := k) r I).toLinearMap).comp
        (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap (A ⧸ I)
          (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) Ω[A ⧸ I⁄k] g)).comp
        ((ConormalAdjunction.equivalence I bI bQ).toLinearMap.baseChange
          (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I)) := by
  let := LocalizedConormalBases.quotientFormallyEtale (B := B) r I
  have h := Etale.ConormalResidue.residue_naturality
    (LocalizedQuotientExtension.presentation (k := k) I) (LocalizedQuotientExtension.presentation (k := k) (LocalizedQuotientExtension.extendedIdeal (B := B) I))
    (LocalizedQuotientExtension.map I) rfl (LocalizedQuotientExtension.kernel_bijective I r) (LocalizedQuotientExtension.formallyEtale I r)
    (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) bQ
  rw [conormalBasis_eq r I bI] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalResidue
