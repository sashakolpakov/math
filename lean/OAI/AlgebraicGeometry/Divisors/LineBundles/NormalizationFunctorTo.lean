import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition

/-! # Normalization Functor To -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationFunctorTo.BundleCycles.NormalizationFunctor

noncomputable section

/-! A dominant morphism lifts to the constructed global normalizations.
The lift comes from the relative-normalization universal property applied
to the finite pullback, and commutes with the actual generic field maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

theorem genericMap_square :
    Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ≫ f := by
  rw [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_hom]
  change Spec.map (f.stalkMap (genericPoint X)) ≫
    Spec.map (Y.presheaf.stalkSpecializes (Inseparable.of_eq hη).specializes) ≫ Y.fromSpecStalk (genericPoint Y) = _
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  rfl

def genericLift : Spec X.functionField ⟶ pullback f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) :=
  pullback.lift (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X)
    (Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).toNormalization) (by
      change IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ≫ f =
        (Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).toNormalization) ≫
          (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).fromNormalization
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
      exact (genericMap_square f hη).symm)

theorem genericLift_fst :
    IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X = genericLift f hη ≫ pullback.fst f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) := by
  exact (pullback.lift_fst _ _ _).symm

def normalizationLiftToPullback : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X ⟶ pullback f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) :=
  (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).normalizationDesc (genericLift f hη)
    (pullback.fst f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y)) (genericLift_fst f hη)

theorem normalizationLiftToPullback_fst :
    normalizationLiftToPullback f hη ≫ pullback.fst f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) =
      IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X :=
  Scheme.Hom.normalizationDesc_comp _ _ _ _

theorem toNormalization_normalizationLiftToPullback :
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization ≫ normalizationLiftToPullback f hη =
      genericLift f hη :=
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

def normalizationLift : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X ⟶ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y :=
  normalizationLiftToPullback f hη ≫ pullback.snd f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y)

theorem normalizationLift_comp :
    normalizationLift f hη ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y = IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f := by
  rw [normalizationLift, Category.assoc, ← pullback.condition, ← Category.assoc,
    normalizationLiftToPullback_fst]

theorem toNormalization_normalizationLift :
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization ≫ normalizationLift f hη =
      Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) ≫ (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).toNormalization := by
  exact (Category.assoc
    (show Spec X.functionField ⟶ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X from (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization)
    (normalizationLiftToPullback f hη) (pullback.snd f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y))).symm.trans
      ((congrArg (fun k : Spec X.functionField ⟶ pullback f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) =>
        k ≫ pullback.snd f (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y))
          (toNormalization_normalizationLiftToPullback f hη)).trans (pullback.lift_snd _ _ _))

theorem normalizationLift_genericPoint :
    normalizationLift f hη (genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)) = genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y) := by
  rw [← IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X]
  change ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization ≫ normalizationLift f hη)
    (genericPoint (Spec X.functionField)) = _
  rw [toNormalization_normalizationLift]
  let : Subsingleton (Spec Y.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Y.functionField))
  have h : (Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)) (genericPoint (Spec X.functionField)) =
      genericPoint (Spec Y.functionField) := Subsingleton.elim _ _
  change (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).toNormalization
    ((Spec.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)) (genericPoint (Spec X.functionField))) = _
  rw [h, IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint]

theorem normalizationLift_isFinite {k : Type u} [Field k] [CharZero k]
    (gX : X ⟶ Spec (.of k)) [LocallyOfFiniteType gX] [IsFinite f] :
    IsFinite (normalizationLift f hη) := by
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X gX
  let : IsFinite (normalizationLift f hη ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) := by
    rw [normalizationLift_comp]
    infer_instance
  exact IsFinite.of_comp (normalizationLift f hη) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y)

theorem normalizationFieldMap_square :
    IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap Y ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (normalizationLift f hη) (normalizationLift_genericPoint f hη) =
        Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη ≫ IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap X := by
  rw [IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap, IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap,
    ← GenericFieldComposition.BundleCycles.genericFieldMap_comp, ← GenericFieldComposition.BundleCycles.genericFieldMap_comp]
  exact GenericFieldComposition.BundleCycles.genericFieldMap_congr (normalizationLift_comp f hη) _ _

theorem normalizationLift_norm (g : X.functionField) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (normalizationLift f hη)
      (normalizationLift_genericPoint f hη)).hom.toAlgebra
    (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso Y).hom (Algebra.norm Y.functionField g) =
      Algebra.norm (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y).functionField ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (normalizationLift f hη)
    (normalizationLift_genericPoint f hη)).hom.toAlgebra
  have h := Algebra.norm_eq_of_equiv_equiv
    (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso Y).commRingCatIsoToRingEquiv
    (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (normalizationFieldMap_square f hη)) g
  exact (RingEquiv.eq_symm_apply (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso Y).commRingCatIsoToRingEquiv).mp h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationFunctorTo.BundleCycles.NormalizationFunctor
