import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedAmbientExteriorRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBasisTransport

/-! # Localized Residue Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedResidueRestriction.Conormal

noncomputable section

/-! Pointwise localization of the genuine smooth quotient residue,
including transport to the named ideal on a restricted affine open. -/

open _root_.CategoryTheory _root_.Module
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedQuotientExtension OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (r : A) [IsLocalization.Away r B] (I : Ideal A)

local instance restrictionBaseTower : IsScalarTower k (A ⧸ I) (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) :=
  AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I

def quotientHom (J : Ideal B) (hJ : I.map (algebraMap A B) = J) :
    CommAlgCat.of k (A ⧸ I) ⟶ CommAlgCat.of k (B ⧸ J) :=
  CommAlgCat.ofHom (Ideal.quotientMapₐ J (IsScalarTower.toAlgHom k A B)
    (by intro a ha; exact hJ ▸ Ideal.mem_map_of_mem _ ha))

theorem quotientHom_eq : quotientHom (k := k) I (LocalizedQuotientExtension.extendedIdeal (B := B) I) rfl =
    Exterior.KaehlerBaseChange.algebraHom (k := k)
      (A := A ⧸ I) (B := B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

def exteriorRestrictionOfEq (J : Ideal B) (hJ : I.map (algebraMap A B) = J)
    (n : ℕ) (x : ⋀[A ⧸ I]^n ((A ⧸ I) ⊗[A] Ω[A⁄k])) :
    ⋀[B ⧸ J]^n ((B ⧸ J) ⊗[B] Ω[B⁄k]) :=
  hJ ▸ LocalizedAmbientExteriorRestriction.ConormalResidue.exteriorMap (k := k) (B := B) r I n (1 ⊗ₜ[A ⧸ I] x)

variable [Algebra.Smooth k A] [Algebra.Smooth k (A ⧸ I)] [Algebra.Smooth k B]
  {c g : ℕ} (bI : Basis (Fin c) (A ⧸ I) I.Cotangent)
  (bQ : Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k])

theorem residue_one [Algebra.Smooth k (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I)]
    (x : ⋀[A ⧸ I]^(c + g) ((A ⧸ I) ⊗[A] Ω[A⁄k])) :
    ConormalAdjunction.equivalence (LocalizedQuotientExtension.extendedIdeal (B := B) I)
      (LocalizedConormalBases.conormalBasis r I bI)
      (LocalizedConormalBases.quotientBasis r I bQ)
        (LocalizedAmbientExteriorRestriction.ConormalResidue.exteriorMap (k := k) (B := B) r I (c + g) (1 ⊗ₜ[A ⧸ I] x)) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (quotientHom (k := k) I (LocalizedQuotientExtension.extendedIdeal (B := B) I) rfl) g
      (ConormalAdjunction.equivalence I bI bQ x) := by
  let := LocalizedConormalBases.quotientFormallyEtale (B := B) r I
  have h := LinearMap.congr_fun (LocalizedConormalResidue.residue_naturality (B := B) r I bI bQ)
    ((1 : B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) ⊗ₜ[A ⧸ I] x)
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe] at h
  rw [quotientHom_eq]
  exact h.trans (Exterior.KaehlerBaseChange.etale_map_one g _)

theorem residue_restriction (J : Ideal B) (hJ : I.map (algebraMap A B) = J)
    [Algebra.Smooth k (B ⧸ J)]
    (x : ⋀[A ⧸ I]^(c + g) ((A ⧸ I) ⊗[A] Ω[A⁄k])) :
    ConormalAdjunction.equivalence J
      (LocalizedConormalBasisTransport.Bases.conormalBasisOfEq r I J hJ bI)
      (LocalizedConormalBasisTransport.Bases.quotientBasisOfEq r I J hJ bQ)
        (exteriorRestrictionOfEq r I J hJ (c + g) x) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (quotientHom (k := k) I J hJ) g
      (ConormalAdjunction.equivalence I bI bQ x) := by
  subst J
  exact residue_one r I bI bQ x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedResidueRestriction.Conormal
