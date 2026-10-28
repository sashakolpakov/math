import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Fields

/-! # Functor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Functor

noncomputable section

/-! A dominant morphism lifts to the constructed global normalizations.
The lift comes from the relative-normalization universal property applied
to the finite pullback, and commutes with the actual generic field maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

theorem genericMap_square :
    Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ Normalization.Scheme.genericMap Y = Normalization.Scheme.genericMap X ≫ f := by
  rw [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_hom]
  change Spec.map (f.stalkMap (genericPoint X)) ≫
    Spec.map (Y.presheaf.stalkSpecializes _) ≫ Y.fromSpecStalk (genericPoint Y) = _
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  rfl

def genericLift : Spec X.functionField ⟶ pullback f (Normalization.Scheme.normalizationMap Y) :=
  pullback.lift (Normalization.Scheme.genericMap X)
    (Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ (Normalization.Scheme.genericMap Y).toNormalization) (by
      change Normalization.Scheme.genericMap X ≫ f =
        (Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ (Normalization.Scheme.genericMap Y).toNormalization) ≫
          (Normalization.Scheme.genericMap Y).fromNormalization
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
      exact (genericMap_square f hη).symm)

def normalizationLift : Normalization.Scheme.normalization X ⟶ Normalization.Scheme.normalization Y :=
  (Normalization.Scheme.genericMap X).normalizationDesc (genericLift f hη)
    (pullback.fst f (Normalization.Scheme.normalizationMap Y)) (by simp [genericLift]) ≫
      pullback.snd f (Normalization.Scheme.normalizationMap Y)

theorem normalizationLift_comp :
    normalizationLift f hη ≫ Normalization.Scheme.normalizationMap Y = Normalization.Scheme.normalizationMap X ≫ f := by
  rw [normalizationLift, Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.Hom.normalizationDesc_comp]
  rfl

theorem toNormalization_normalizationLift :
    (Normalization.Scheme.genericMap X).toNormalization ≫ normalizationLift f hη =
      Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ (Normalization.Scheme.genericMap Y).toNormalization := by
  rw [normalizationLift, ← Category.assoc, Scheme.Hom.toNormalization_normalizationDesc]
  simp only [genericLift, pullback.lift_snd]

theorem normalizationLift_genericPoint :
    normalizationLift f hη (genericPoint (Normalization.Scheme.normalization X)) = genericPoint (Normalization.Scheme.normalization Y) := by
  rw [← Normalization.Scheme.toNormalization_genericPoint X]
  change ((Normalization.Scheme.genericMap X).toNormalization ≫ normalizationLift f hη)
    (genericPoint (Spec X.functionField)) = _
  rw [toNormalization_normalizationLift]
  let : Subsingleton (Spec Y.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Y.functionField))
  have h : (Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)) (genericPoint (Spec X.functionField)) =
      genericPoint (Spec Y.functionField) := Subsingleton.elim _ _
  change (Normalization.Scheme.genericMap Y).toNormalization
    ((Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)) (genericPoint (Spec X.functionField))) = _
  rw [h, Normalization.Scheme.toNormalization_genericPoint]

theorem normalizationLift_isProper {k : Type u} [Field k] [CharZero k]
    (gX : X ⟶ Spec (.of k)) [LocallyOfFiniteType gX] [IsProper f] :
    IsProper (normalizationLift f hη) := by
  let : IsFinite (Normalization.Scheme.normalizationMap X) := Normalization.Scheme.normalizationMap_isFinite X gX
  let : IsProper (normalizationLift f hη ≫ Normalization.Scheme.normalizationMap Y) := by
    rw [normalizationLift_comp]
    infer_instance
  exact IsProper.of_comp (normalizationLift f hη) (Normalization.Scheme.normalizationMap Y)

theorem normalizationFieldMap_square :
    Fields.normalizationFieldMap Y ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (normalizationLift f hη) (normalizationLift_genericPoint f hη) =
        Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη ≫ Fields.normalizationFieldMap X := by
  rw [Fields.normalizationFieldMap, Fields.normalizationFieldMap,
    ← Generic.Fields.genericFieldMap_comp, ← Generic.Fields.genericFieldMap_comp]
  exact Generic.Fields.genericFieldMap_congr (normalizationLift_comp f hη) _ _

theorem normalizationLift_norm (g : X.functionField) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (normalizationLift f hη)
      (normalizationLift_genericPoint f hη)).hom.toAlgebra
    (Fields.normalizationFieldIso Y).hom (Algebra.norm Y.functionField g) =
      Algebra.norm (Normalization.Scheme.normalization Y).functionField ((Fields.normalizationFieldIso X).hom g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (normalizationLift f hη)
    (normalizationLift_genericPoint f hη)).hom.toAlgebra
  have h := Algebra.norm_eq_of_equiv_equiv
    (Fields.normalizationFieldIso Y).commRingCatIsoToRingEquiv
    (Fields.normalizationFieldIso X).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (normalizationFieldMap_square f hη)) g
  exact (RingEquiv.eq_symm_apply (Fields.normalizationFieldIso Y).commRingCatIsoToRingEquiv).mp h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Functor
