import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Normalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.KrullDimension.Field

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

noncomputable section

/-! The actual normalization scheme is the relative normalization of the
generic-point morphism. Its affine rings are the finite integral closures
already constructed, so the normalization morphism is finite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (X : Scheme.{u}) [IsIntegral X]

def genericMap : Spec X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)

instance : QuasiCompact (genericMap X) := by
  unfold genericMap
  infer_instance

instance : QuasiSeparated (genericMap X) := by
  unfold genericMap
  infer_instance

def normalization : Scheme := (genericMap X).normalization

def normalizationMap : ProjectionFormula.Normalization.Scheme.normalization X ⟶ X := (genericMap X).fromNormalization

instance : IsIntegral (ProjectionFormula.Normalization.Scheme.normalization X) := by
  unfold ProjectionFormula.Normalization.Scheme.normalization
  infer_instance

instance : IsIntegralHom (normalizationMap X) := by
  dsimp [normalizationMap, ProjectionFormula.Normalization.Scheme.normalization]
  infer_instance

theorem genericMap_apply (x : Spec X.functionField) : genericMap X x = genericPoint X := by
  let : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  have hx : x = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  rw [hx]
  exact Scheme.fromSpecStalk_closedPoint

instance genericMap_isDominant : IsDominant (genericMap X) := by
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_spec X]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint X.functionField, genericMap_apply X _⟩

instance normalizationMap_isDominant : IsDominant (normalizationMap X) := by
  let : IsDominant ((genericMap X).toNormalization ≫ (genericMap X).fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp (genericMap X).toNormalization (genericMap X).fromNormalization

theorem normalizationMap_surjective : Function.Surjective (normalizationMap X) := by
  let : Surjective (normalizationMap X) :=
    surjective_of_isDominant_of_isClosed_range (normalizationMap X)
      ((normalizationMap X).isClosedMap.isClosed_range)
  exact (normalizationMap X).surjective

theorem toNormalization_genericPoint :
    (genericMap X).toNormalization (genericPoint (Spec X.functionField)) =
      genericPoint (ProjectionFormula.Normalization.Scheme.normalization X) := by
  let t : Spec X.functionField ⟶ ProjectionFormula.Normalization.Scheme.normalization X := (genericMap X).toNormalization
  change t (genericPoint (Spec X.functionField)) = genericPoint (ProjectionFormula.Normalization.Scheme.normalization X)
  apply IsGenericPoint.eq _ (genericPoint_spec (ProjectionFormula.Normalization.Scheme.normalization X))
  have h := (genericPoint_spec (Spec X.functionField)).image
    t.continuous
  have ht : closure (Set.range t) = Set.univ :=
    (genericMap X).toNormalization.denseRange.closure_range
  simpa only [Set.image_univ, ht] using h

/-- The finite normalization has generic residue-field degree one. -/
theorem normalizationMap_generic_residueDegree :
    (normalizationMap X).residueDegree (genericPoint (ProjectionFormula.Normalization.Scheme.normalization X)) = 1 := by
  let : IsPreimmersion (genericMap X) := by unfold genericMap; infer_instance
  have h := CyclePushforward.residueDegree_comp (genericMap X).toNormalization
    (genericMap X).fromNormalization (genericPoint (Spec X.functionField))
  rw [Scheme.Hom.toNormalization_fromNormalization,
    Principal.ClosedSectionCycle.residueDegree_immersion, toNormalization_genericPoint] at h
  exact Nat.eq_one_of_dvd_one ⟨_, h⟩

theorem genericMap_preimage (U : X.Opens) [Nonempty U] :
    genericMap X ⁻¹ᵁ U = ⊤ := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change genericMap X x ∈ U ↔ True
  rw [genericMap_apply]
  exact iff_of_true
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (show Nonempty U from inferInstance))) trivial

def preimageFieldIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, genericMap X ⁻¹ᵁ U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso (eqToIso (genericMap_preimage X U).symm).op ≪≫
    Scheme.ΓSpecIso X.functionField

theorem genericMap_app (U : X.Opens) [Nonempty U] :
    (genericMap X).app U = X.germToFunctionField U ≫ (preimageFieldIso X U).inv := by
  change (X.fromSpecStalk (genericPoint X)).app U = _
  rw [Scheme.fromSpecStalk_app
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (show Nonempty U from inferInstance)))]
  rfl

def preimageFieldAlgEquiv (U : X.Opens) [Nonempty U] :
    letI := ((genericMap X).app U).hom.toAlgebra
    Γ(Spec X.functionField, genericMap X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField := by
  let := ((genericMap X).app U).hom.toAlgebra
  refine { (preimageFieldIso X U).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  change (preimageFieldIso X U).hom ((genericMap X).app U a) =
    X.germToFunctionField U a
  rw [genericMap_app]
  simp

theorem finite_normalization_affineRing {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((genericMap X).app U).hom.toAlgebra
    Module.Finite Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec X.functionField, genericMap X ⁻¹ᵁ U)) := by
  let := ((genericMap X).app U).hom.toAlgebra
  let C := Γ(Spec X.functionField, genericMap X ⁻¹ᵁ U)
  let e : C ≃+* X.functionField := (preimageFieldIso X U).commRingCatIsoToRingEquiv
  let : Field C := (MulEquiv.isField (Field.toIsField X.functionField) e.toMulEquiv).toField
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsFractionRing Γ(X, U) C :=
    IsFractionRing.of_algEquiv (preimageFieldAlgEquiv X U).symm
  exact ProjectionFormula.Finite.Normalization.finite_integralClosure k Γ(X, U) C

/-- The normalization morphism of an integral scheme locally of finite
type over a characteristic-zero field is finite. -/
theorem normalizationMap_isFinite {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsFinite (normalizationMap X) := by
  refine
    { toIsAffineHom := inferInstance
      finite_app := ?_ }
  intro U hU
  by_cases hbot : U = ⊥
  · subst U
    have hpre : normalizationMap X ⁻¹ᵁ (⊥ : X.Opens) = ⊥ := by simp
    let : Subsingleton Γ(ProjectionFormula.Normalization.Scheme.normalization X, normalizationMap X ⁻¹ᵁ (⊥ : X.Opens)) := by
      rw [hpre]
      infer_instance
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)
  · let : Nonempty U := Set.nonempty_coe_sort.mpr ((U.ne_bot_iff_nonempty).mp hbot)
    let := ((genericMap X).app U).hom.toAlgebra
    let := finite_normalization_affineRing X f U hU
    change ((genericMap X).fromNormalization.app U).hom.Finite
    rw [(genericMap X).fromNormalization_app hU, CommRingCat.hom_comp,
      RingHom.finite_respectsIso.cancel_right_isIso]
    exact RingHom.finite_algebraMap.mpr inferInstance

theorem normalization_affineSections_integrallyClosed
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(ProjectionFormula.Normalization.Scheme.normalization X, normalizationMap X ⁻¹ᵁ U) := by
  let := ((genericMap X).app U).hom.toAlgebra
  let C := Γ(Spec X.functionField, genericMap X ⁻¹ᵁ U)
  let e : C ≃+* X.functionField := (preimageFieldIso X U).commRingCatIsoToRingEquiv
  let : Field C := (MulEquiv.isField (Field.toIsField X.functionField) e.toMulEquiv).toField
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsFractionRing Γ(X, U) C :=
    IsFractionRing.of_algEquiv (preimageFieldAlgEquiv X U).symm
  let : IsIntegrallyClosed (integralClosure Γ(X, U) C) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := Γ(X, U)) C
  exact IsIntegrallyClosed.of_equiv
    ((genericMap X).normalizationObjIso hU).symm.commRingCatIsoToRingEquiv

/-- All local rings of the constructed normalization are integrally closed. -/
theorem normalization_stalk_integrallyClosed (y : ProjectionFormula.Normalization.Scheme.normalization X) :
    IsIntegrallyClosed ((ProjectionFormula.Normalization.Scheme.normalization X).presheaf.stalk y) := by
  let x : X := normalizationMap X y
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let : Nonempty U := ⟨⟨x, X.affineCover.covers x⟩⟩
  let V : (ProjectionFormula.Normalization.Scheme.normalization X).Opens := normalizationMap X ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (normalizationMap X)
  let y' : V := ⟨y, X.affineCover.covers x⟩
  let : Nonempty V := ⟨y'⟩
  let : IsIntegrallyClosed Γ(ProjectionFormula.Normalization.Scheme.normalization X, V) :=
    normalization_affineSections_integrallyClosed X U hU
  let := TopCat.Presheaf.algebra_section_stalk (ProjectionFormula.Normalization.Scheme.normalization X).presheaf y'
  let := hV.isLocalization_stalk y'
  exact isIntegrallyClosed_of_isLocalization ((ProjectionFormula.Normalization.Scheme.normalization X).presheaf.stalk y)
    (hV.primeIdealOf y').asIdeal.primeCompl
    (hV.primeIdealOf y').asIdeal.primeCompl_le_nonZeroDivisors

/-- The codimension-one local rings of the finite normalization are DVRs. -/
theorem normalization_stalk_isDVR {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : ProjectionFormula.Normalization.Scheme.normalization X) (hy : Order.coheight y = 1) :
    IsDiscreteValuationRing ((ProjectionFormula.Normalization.Scheme.normalization X).presheaf.stalk y) := by
  let : IsFinite (normalizationMap X) := normalizationMap_isFinite X f
  let : IsLocallyNoetherian (ProjectionFormula.Normalization.Scheme.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationMap X ≫ f)
  let R := (ProjectionFormula.Normalization.Scheme.normalization X).presheaf.stalk y
  let : IsIntegrallyClosed R := normalization_stalk_integrallyClosed X y
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hy.le
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
    change ringKrullDim ((ProjectionFormula.Normalization.Scheme.normalization X).presheaf.stalk y) = 0 at hzero
    rw [ringKrullDim_stalk_eq_coheight, hy] at hzero
    exact (by decide : (1 : WithBot ℕ∞) ≠ 0) hzero
  have ht : IsDiscreteValuationRing R ↔ IsDedekindDomain R :=
    (IsDiscreteValuationRing.TFAE R hn).out 1 3
  exact ht.mpr (show IsDedekindDomain R from inferInstance)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme
