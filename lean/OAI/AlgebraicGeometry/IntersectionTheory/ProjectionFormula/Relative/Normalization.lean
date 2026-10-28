import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.FieldNormalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Normalization

noncomputable section

/-! Normalize an integral scheme in a finite extension of its actual
function field. The scheme and its finite morphism are constructed from
relative normalization, with affine rings given by integral closures. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]

def fieldGenericMap : Spec (.of L) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
    Normalization.Scheme.genericMap Y

instance : QuasiCompact (fieldGenericMap Y L) := by
  unfold fieldGenericMap
  infer_instance

instance : QuasiSeparated (fieldGenericMap Y L) := by
  unfold fieldGenericMap
  infer_instance

def relativeNormalization : Scheme := (fieldGenericMap Y L).normalization

def relativeNormalizationMap : relativeNormalization Y L ⟶ Y :=
  (fieldGenericMap Y L).fromNormalization

instance : IsIntegral (relativeNormalization Y L) := by
  unfold relativeNormalization
  infer_instance

instance : IsIntegralHom (relativeNormalizationMap Y L) := by
  unfold relativeNormalizationMap relativeNormalization
  infer_instance

theorem fieldGenericMap_apply (x : Spec (.of L)) : fieldGenericMap Y L x = genericPoint Y :=
  Normalization.Scheme.genericMap_apply Y _

theorem fieldGenericMap_preimage (U : Y.Opens) [Nonempty U] : fieldGenericMap Y L ⁻¹ᵁ U = ⊤ := by
  apply Opens.ext
  apply Set.ext
  intro x
  change fieldGenericMap Y L x ∈ U ↔ True
  rw [fieldGenericMap_apply]
  exact iff_of_true (((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))) trivial

def preimageFieldIso (U : Y.Opens) [Nonempty U] :
    Γ(Spec (.of L), fieldGenericMap Y L ⁻¹ᵁ U) ≅ .of L :=
  (Spec (.of L)).presheaf.mapIso (eqToIso (fieldGenericMap_preimage Y L U).symm).op ≪≫
    Scheme.ΓSpecIso (.of L)

theorem fieldGenericMap_app (U : Y.Opens) [Nonempty U] :
    (fieldGenericMap Y L).app U =
      Y.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap Y.functionField L) ≫
        (preimageFieldIso Y L U).inv := by
  change (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
    Normalization.Scheme.genericMap Y).app U = _
  rw [Scheme.Hom.comp_app]
  rw [Normalization.Scheme.genericMap_app]
  simp [Normalization.Scheme.preimageFieldIso, preimageFieldIso,
    Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  congr 4

local instance (U : Y.Opens) [Nonempty U] : Algebra Γ(Y, U) L :=
  ((algebraMap Y.functionField L).comp (algebraMap Γ(Y, U) Y.functionField)).toAlgebra

local instance (U : Y.Opens) [Nonempty U] : IsScalarTower Γ(Y, U) Y.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

def preimageFieldAlgEquiv (U : Y.Opens) [Nonempty U] :
    letI := ((fieldGenericMap Y L).app U).hom.toAlgebra
    Γ(Spec (.of L), fieldGenericMap Y L ⁻¹ᵁ U) ≃ₐ[Γ(Y, U)] L := by
  let := ((fieldGenericMap Y L).app U).hom.toAlgebra
  refine { (preimageFieldIso Y L U).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  change (preimageFieldIso Y L U).hom ((fieldGenericMap Y L).app U a) =
    algebraMap Y.functionField L (Y.germToFunctionField U a)
  rw [fieldGenericMap_app]
  simp

variable [Module.Finite Y.functionField L]

theorem finite_affineRing {k : Type u} [Field k] [CharZero k]
    (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((fieldGenericMap Y L).app U).hom.toAlgebra
    Module.Finite Γ(Y, U)
      (integralClosure Γ(Y, U) Γ(Spec (.of L), fieldGenericMap Y L ⁻¹ᵁ U)) := by
  let := ((fieldGenericMap Y L).app U).hom.toAlgebra
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) L) :=
    ProjectionFormula.Finite.FieldNormalization.finite_integralClosure_extension k Γ(Y, U) Y.functionField L
  let e := (preimageFieldAlgEquiv Y L U).mapIntegralClosure
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- The intermediate normalization morphism is finite, proved on every
affine chart from the finite integral-closure theorem. -/
theorem relativeNormalizationMap_isFinite {k : Type u} [Field k] [CharZero k]
    (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsFinite (relativeNormalizationMap Y L) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hbot : U = ⊥
  · subst U
    have hpre : relativeNormalizationMap Y L ⁻¹ᵁ (⊥ : Y.Opens) = ⊥ := by simp
    let : Subsingleton Γ(relativeNormalization Y L,
        relativeNormalizationMap Y L ⁻¹ᵁ (⊥ : Y.Opens)) := by
      rw [hpre]
      infer_instance
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)
  · let : Nonempty U := Set.nonempty_coe_sort.mpr ((U.ne_bot_iff_nonempty).mp hbot)
    let := ((fieldGenericMap Y L).app U).hom.toAlgebra
    let := finite_affineRing Y L f U hU
    change ((fieldGenericMap Y L).fromNormalization.app U).hom.Finite
    rw [(fieldGenericMap Y L).fromNormalization_app hU, CommRingCat.hom_comp,
      RingHom.finite_respectsIso.cancel_right_isIso]
    exact RingHom.finite_algebraMap.mpr inferInstance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Normalization
