import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFactorization
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedTransformMap
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Principality

/-! # Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Transform.Construction

noncomputable section

/-! Actual controlled transforms of retained native coefficient ideals on the transformed carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

local instance retainedCarrierNoetherian (I H : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsLocallyNoetherian (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι

def globalControlledCarrierMap (I H : X.IdealSheafData) (hI : I ≠ ⊥) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme ⟶ H.subscheme := by
  have ht : H.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≤ GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1 :=
    GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I H 1 (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
  exact ClosedTransformMap.Construction.closedTransformMap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) H (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1) ht

theorem globalControlledCarrierMap_over (I H : X.IdealSheafData) (hI : I ≠ ⊥) :
    globalControlledCarrierMap I H hI ≫ H.subschemeι =
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI :=
  ClosedTransformMap.Construction.closedTransformMap_over _ _ _ _

def globalRetainedCoefficientTransform
    (I H : X.IdealSheafData) (C : H.subscheme.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme.IdealSheafData :=
  GlobalControlled.Ideal.Construction.controlledIdealSheaf (I.comap H.subschemeι) C b.factorial (globalControlledCarrierMap I H hI)

theorem closedTransformMap_center_locallyPrincipal
    (I H : X.IdealSheafData) (hI : I ≠ ⊥) :
    Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf ((I.comap H.subschemeι).comap (globalControlledCarrierMap I H hI)) := by
  rw [← Scheme.IdealSheafData.comap_comp, globalControlledCarrierMap_over,
    Scheme.IdealSheafData.comap_comp]
  exact (Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal I hI).comap _

theorem globalRetainedCoefficientTransform_factorization
    (I H : X.IdealSheafData) (C : H.subscheme.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ)
    (hp : C ≤ (I.comap H.subschemeι) ^ b.factorial) :
    let r := globalControlledCarrierMap I H hI
    ((I.comap H.subschemeι).comap r) ^ b.factorial * globalRetainedCoefficientTransform I H C hI b =
      C.comap r := by
  intro r
  change ((I.comap H.subschemeι).comap r) ^ b.factorial *
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (C.comap r) (((I.comap H.subschemeι).comap r) ^ b.factorial) = C.comap r
  apply Locally.PrincipalColonFactorization.Construction.locallyPrincipal_noetherianIdealSheafColon_factorization
  · exact (closedTransformMap_center_locallyPrincipal I H hI).pow b.factorial
  · have h := Scheme.IdealSheafData.comap_mono r hp
    change C.comap r ≤ ((I.comap H.subschemeι) ^ b.factorial).comap r at h
    rwa [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow] at h

theorem globalRetainedCoefficientTransform_comap_regular_chart
    (I H : X.IdealSheafData) (C : H.subscheme.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ)
    (hp : C ≤ (I.comap H.subschemeι) ^ b.factorial)
    (R : CommRingCat) (j : Spec R ⟶ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme)
    (A : Ideal R) (c : R) (hc : IsRegular c) :
    let r := globalControlledCarrierMap I H hI
    (C.comap r).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel A →
    ((I.comap H.subschemeι).comap r).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {c}) →
    (globalRetainedCoefficientTransform I H C hI b).comap j =
      Affine.QuotientKernel.Construction.affineQuotientKernel (A.colon (Ideal.span {c ^ b.factorial} : Set R)) := by
  intro r hC hI'
  apply Locally.PrincipalColonFactorization.Construction.idealSheaf_factorization_comap_regular_affine _ _ _
    (globalRetainedCoefficientTransform_factorization I H C hI b hp) R j A (c ^ b.factorial) hC
  · rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, hI', ← Affine.QuotientKernel.Construction.affineQuotientKernel_pow, Ideal.span_singleton_pow]
  · exact hc.pow b.factorial

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Transform.Construction
