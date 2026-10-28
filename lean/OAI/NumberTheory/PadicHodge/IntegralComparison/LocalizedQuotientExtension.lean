import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedExtensionKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBases
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective

/-! # Localized Quotient Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedQuotientExtension

noncomputable section

/-! Actual quotient extensions under localization, with no kernel
base-change hypothesis left to supply. Their cotangent maps are the
original maps on ideal classes. -/

open scoped TensorProduct

open _root_.Algebra.Extension

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (I : Ideal A)

abbrev presentation : Algebra.Extension.{u} k (A ⧸ I) :=
  .ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective

abbrev extendedIdeal : Ideal B := I.map (algebraMap A B)

local instance baseTower : IsScalarTower k (A ⧸ I) (B ⧸ extendedIdeal (B := B) I) :=
  AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I

local instance presentationAlgebra :
    Algebra (presentation (k := k) I).Ring (presentation (k := k) (extendedIdeal (B := B) I)).Ring :=
  inferInstanceAs (Algebra A B)

def map : (presentation (k := k) I).Hom (presentation (k := k) (extendedIdeal (B := B) I)) where
  toRingHom := algebraMap A B
  toRingHom_algebraMap x := (IsScalarTower.algebraMap_apply k A B x).symm
  algebraMap_toRingHom _ := rfl

theorem ker_eq : (presentation (k := k) I).ker = I :=
  Ideal.mk_ker

omit [IsScalarTower k A B] in
theorem kernel_map :
    (presentation (k := k) I).ker.map (algebraMap A B) =
      (presentation (k := k) (extendedIdeal (B := B) I)).ker := by
  rw [ker_eq, ker_eq]

variable (r : A) [IsLocalization.Away r B]

local instance presentationLocalization :
    IsLocalization.Away (show (presentation (k := k) I).Ring from r)
      (presentation (k := k) (extendedIdeal (B := B) I)).Ring :=
  inferInstanceAs (IsLocalization.Away r B)

include r in
theorem formallyEtale : (LocalizedQuotientExtension.map (k := k) (B := B) I).toRingHom.FormallyEtale :=
  show (algebraMap A B).FormallyEtale from
    RingHom.formallyEtale_algebraMap.mpr
      (Algebra.FormallyEtale.of_isLocalization (Rₘ := B) (Submonoid.powers r))

include r in
theorem kernel_bijective : Function.Bijective
    (((LocalizedQuotientExtension.map (k := k) (B := B) I).mapKer rfl).liftBaseChange
      (presentation (k := k) (extendedIdeal (B := B) I)).Ring) :=
  LocalizedExtensionKernel.kernel_bijective
    (presentation (k := k) I) (presentation (k := k) (extendedIdeal (B := B) I))
    (LocalizedQuotientExtension.map (k := k) (B := B) I) rfl (Submonoid.powers r) (kernel_map (k := k) (B := B) I)

omit [Algebra k B] [IsScalarTower k A B] [IsLocalization.Away r B] in
theorem idealEquiv_mk (x : (presentation (k := k) I).ker) :
    AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I (Cotangent.mk x) =
      I.toCotangent ⟨x.val, Ideal.Quotient.eq_zero_iff_mem.mp x.property⟩ := by
  rfl

omit [IsLocalization.Away r B] in
theorem idealEquiv_map (x : (presentation (k := k) I).Cotangent) :
    AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) (extendedIdeal (B := B) I)
      (Cotangent.map (LocalizedQuotientExtension.map (k := k) (B := B) I) x) =
      AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap (S := B) I
        (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I x) := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedQuotientExtension
