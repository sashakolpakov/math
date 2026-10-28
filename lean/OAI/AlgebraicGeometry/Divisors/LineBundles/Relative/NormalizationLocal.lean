import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization

/-! # Normalization Local -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal

noncomputable section

/-! The finite intermediate normalization has normal local rings and DVR
local rings at its divisor points. Its affine charts use the integral
closure in the specified finite function-field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]

local instance (U : Y.Opens) [Nonempty U] : Algebra Γ(Y, U) L :=
  ((algebraMap Y.functionField L).comp (algebraMap Γ(Y, U) Y.functionField)).toAlgebra

local instance (U : Y.Opens) [Nonempty U] : IsScalarTower Γ(Y, U) Y.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

def affineRingIso (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Γ(Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L, Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(Y, U) L) := by
  let := ((Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).app U).hom.toAlgebra
  exact (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).normalizationObjIso hU ≪≫
    (Normalization.BundleCycles.RelativeNormalization.preimageFieldAlgEquiv Y L U).mapIntegralClosure.toRingEquiv.toCommRingCatIso

theorem affineRingIso_base (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L).app U ≫ (affineRingIso Y L U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) L)) := by
  let := ((Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).app U).hom.toAlgebra
  change (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).fromNormalization.app U ≫
    ((Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).normalizationObjIso hU ≪≫
      (Normalization.BundleCycles.RelativeNormalization.preimageFieldAlgEquiv Y L U).mapIntegralClosure.toRingEquiv.toCommRingCatIso).hom = _
  rw [(Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).fromNormalization_app hU, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  ext a
  exact congrArg (fun z : integralClosure Γ(Y, U) L => (z : L))
    ((Normalization.BundleCycles.RelativeNormalization.preimageFieldAlgEquiv Y L U).mapIntegralClosure.commutes a)

variable [Module.Finite Y.functionField L]

theorem affineSections_integrallyClosed (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L, Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) := by
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : IsIntegrallyClosed (integralClosure Γ(Y, U) L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := Γ(Y, U)) Y.functionField
  exact IsIntegrallyClosed.of_equiv (affineRingIso Y L U hU).symm.commRingCatIsoToRingEquiv

theorem stalk_integrallyClosed (z : Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) :
    IsIntegrallyClosed ((Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).presheaf.stalk z) := by
  let y : Y := Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.f _)
  let : Nonempty U := ⟨⟨y, Y.affineCover.covers y⟩⟩
  let V : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).Opens := Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
  let z' : V := ⟨z, Y.affineCover.covers y⟩
  let : Nonempty V := ⟨z'⟩
  let : IsIntegrallyClosed Γ(Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L, V) :=
    affineSections_integrallyClosed Y L U hU
  let := TopCat.Presheaf.algebra_section_stalk (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).presheaf z'
  let := hV.isLocalization_stalk z'
  exact isIntegrallyClosed_of_isLocalization ((Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).presheaf.stalk z)
    (hV.primeIdealOf z').asIdeal.primeCompl
    (hV.primeIdealOf z').asIdeal.primeCompl_le_nonZeroDivisors

theorem stalk_isDVR {k : Type u} [Field k] [CharZero k]
    (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (z : Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) (hz : Order.coheight z = 1) :
    IsDiscreteValuationRing ((Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).presheaf.stalk z) := by
  let : IsFinite (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L) := Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap_isFinite Y L f
  let : IsLocallyNoetherian (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ≫ f)
  let R := (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).presheaf.stalk z
  let : IsIntegrallyClosed R := stalk_integrallyClosed Y L z
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hz.le
  let : Ring.DimensionLEOne R := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let : IsDedekindDomain R :=
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }
  have hn : ¬ IsField R := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    change ringKrullDim ((Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).presheaf.stalk z) = 0 at hzero
    rw [ringKrullDim_stalk_eq_coheight, hz] at hzero
    exact (by decide : (1 : WithBot ℕ∞) ≠ 0) hzero
  have ht : IsDiscreteValuationRing R ↔ IsDedekindDomain R :=
    (IsDiscreteValuationRing.TFAE R hn).out 1 3
  exact ht.mpr (show IsDedekindDomain R from inferInstance)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal
