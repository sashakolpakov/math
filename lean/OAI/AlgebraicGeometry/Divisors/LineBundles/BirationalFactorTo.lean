import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationFields
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationFunctorTo
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

/-! # Birational Factor To -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactor

/-! A dominant proper map factors, after normalizing its source, through
the target's normalization in the source function field. The first map
is birational and proper; the second is finite for a finite field extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization
  Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields

theorem toNormalization_fieldMap_isIso (X : Scheme.{0}) [IsIntegral X] :
    IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization (IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X)) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X)).hom.toAlgebra
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
  apply (IntersectionTheory.ProjectionFormula.Support.Fields.genericFieldMap_finrank_eq_residueDegree
    (show Spec X.functionField ⟶ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X from (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization)
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X)).trans
  let : IsPreimmersion (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X) := by unfold IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap; infer_instance
  have h := IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) (genericPoint (Spec X.functionField))
  change ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization ≫ (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).fromNormalization).residueDegree _ = _ at h
  rw [Scheme.Hom.toNormalization_fromNormalization,
    IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion] at h
  exact Nat.eq_one_of_dvd_one ⟨_, h.trans (Nat.mul_comm _ _)⟩

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

def intermediate : Scheme :=
  letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y X.functionField

instance intermediate_integral : IsIntegral (intermediate f hη) := by
  unfold intermediate
  infer_instance

def intermediateMap : intermediate f hη ⟶ Y :=
  letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y X.functionField

instance intermediateMap_integral : IsIntegralHom (intermediateMap f hη) := by
  unfold intermediateMap intermediate
  infer_instance

def intermediateGenericMap : Spec X.functionField ⟶ intermediate f hη :=
  letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization Y X.functionField

theorem intermediateGenericMap_genericPoint :
    intermediateGenericMap f hη (genericPoint (Spec X.functionField)) =
      genericPoint (intermediate f hη) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  exact Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_genericPoint Y X.functionField

def genericLift : Spec X.functionField ⟶ pullback f (intermediateMap f hη) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  exact pullback.lift (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X) (Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization Y X.functionField) (by
    change IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ≫ f = Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization Y X.functionField ≫
      Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y X.functionField
    rw [Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_comp]
    exact (NormalizationFunctorTo.BundleCycles.NormalizationFunctor.genericMap_square f hη).symm)

theorem genericLift_fst :
    IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X = genericLift f hη ≫ pullback.fst f (intermediateMap f hη) :=
  (pullback.lift_fst _ _ _).symm

def birationalFactorToPullback : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X ⟶ pullback f (intermediateMap f hη) :=
  (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).normalizationDesc (genericLift f hη)
    (pullback.fst f (intermediateMap f hη)) (genericLift_fst f hη)

theorem birationalFactorToPullback_fst :
    birationalFactorToPullback f hη ≫ pullback.fst f (intermediateMap f hη) = IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X :=
  Scheme.Hom.normalizationDesc_comp _ _ _ _

theorem toNormalization_birationalFactorToPullback :
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization ≫ birationalFactorToPullback f hη = genericLift f hη :=
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

def birationalFactor : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X ⟶ intermediate f hη :=
  birationalFactorToPullback f hη ≫ pullback.snd f (intermediateMap f hη)

theorem birationalFactor_comp :
    birationalFactor f hη ≫ intermediateMap f hη = IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f := by
  rw [birationalFactor, Category.assoc, ← pullback.condition, ← Category.assoc,
    birationalFactorToPullback_fst]

theorem toNormalization_birationalFactor :
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization ≫ birationalFactor f hη = intermediateGenericMap f hη := by
  exact (Category.assoc
    (show Spec X.functionField ⟶ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X from (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization)
    (birationalFactorToPullback f hη) (pullback.snd f (intermediateMap f hη))).symm.trans
      ((congrArg (fun k : Spec X.functionField ⟶ pullback f (intermediateMap f hη) =>
        k ≫ pullback.snd f (intermediateMap f hη))
          (toNormalization_birationalFactorToPullback f hη)).trans (pullback.lift_snd _ _ _))

theorem birationalFactor_genericPoint :
    birationalFactor f hη (genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)) =
      genericPoint (intermediate f hη) := by
  rw [← IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X]
  change ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization ≫ birationalFactor f hη) _ = _
  rw [toNormalization_birationalFactor]
  exact intermediateGenericMap_genericPoint f hη

theorem birationalFactor_isFinite {k : Type} [Field k] [CharZero k]
    (gX : X ⟶ Spec (.of k)) [LocallyOfFiniteType gX] [IsFinite f] :
    IsFinite (birationalFactor f hη) := by
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X gX
  let : IsFinite (birationalFactor f hη ≫ intermediateMap f hη) := by
    rw [birationalFactor_comp]
    infer_instance
  exact IsFinite.of_comp (birationalFactor f hη) (intermediateMap f hη)

theorem birationalFactor_fieldMap_isIso :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    Module.Finite Y.functionField X.functionField →
    IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (birationalFactor f hη) (birationalFactor_genericPoint f hη)) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  intro hfinite
  let := hfinite
  let := toNormalization_fieldMap_isIso X
  have h := GenericFieldComposition.BundleCycles.genericFieldMap_comp (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization
    (birationalFactor f hη) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X) (birationalFactor_genericPoint f hη)
  have hc := GenericFieldComposition.BundleCycles.genericFieldMap_congr (toNormalization_birationalFactor f hη)
    ((congrArg (birationalFactor f hη) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X)).trans
      (birationalFactor_genericPoint f hη)) (intermediateGenericMap_genericPoint f hη)
  have hi : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (birationalFactor f hη) (birationalFactor_genericPoint f hη) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).toNormalization (IntersectionTheory.ProjectionFormula.Normalization.Scheme.toNormalization_genericPoint X)) := by
    exact (congrArg (fun k => IsIso k) (h.symm.trans hc)).mpr
      (Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_fieldMap_isIso Y X.functionField)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (toNormalization_fieldMap_isIso X) hi

end AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactor

namespace AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactorFields

/-! Function-field and norm compatibility of the constructed proper
birational factor through the finite intermediate normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

theorem intermediateMap_genericPoint :
    BirationalFactor.intermediateMap f hη (genericPoint (BirationalFactor.intermediate f hη)) = genericPoint Y := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  exact Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint Y X.functionField

theorem factorFieldMap_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη) =
        Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη ≫ IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap X := by
  rw [IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap, ← GenericFieldComposition.BundleCycles.genericFieldMap_comp,
    ← GenericFieldComposition.BundleCycles.genericFieldMap_comp]
  exact GenericFieldComposition.BundleCycles.genericFieldMap_congr (BirationalFactor.birationalFactor_comp f hη) _ _

variable (hfinite : letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Module.Finite Y.functionField X.functionField)

def factorFunctionFieldIso : X.functionField ≅ (BirationalFactor.intermediate f hη).functionField := by
  let := BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  exact IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X ≪≫
    (asIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))).symm

theorem factorFunctionFieldIso_pullback (g : X.functionField) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη)
      ((factorFunctionFieldIso f hη hfinite).hom g) = (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g := by
  let := BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  change (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))
    (inv (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))
      ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g)) = _
  change (inv (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη)) ≫
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))
      ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g) = _
  rw [IsIso.inv_hom_id]
  rfl

theorem factorFunctionFieldIso_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη ≫ (factorFunctionFieldIso f hη hfinite).hom =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη) := by
  let := BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  apply (cancel_mono (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη)
    (BirationalFactor.birationalFactor_genericPoint f hη))).mp
  rw [factorFieldMap_square]
  ext g
  exact factorFunctionFieldIso_pullback f hη hfinite (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g)

theorem factorFunctionFieldIso_norm (g : X.functionField) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη)).hom.toAlgebra
    Algebra.norm Y.functionField ((factorFunctionFieldIso f hη hfinite).hom g) =
      Algebra.norm Y.functionField g := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη)).hom.toAlgebra
  exact (Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl Y.functionField)
    (factorFunctionFieldIso f hη hfinite).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (factorFunctionFieldIso_square f hη hfinite).symm) g).symm

end AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactorFields

end

end OAI
