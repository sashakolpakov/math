import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Functor

/-! # Birational Factor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactor

noncomputable section

/-! A dominant proper map factors, after normalizing its source, through
the target's normalization in the source function field. The first map
is birational and proper; the second is finite for a finite field extension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Normalization
  Relative.NormalizationFields

universe u

theorem toNormalization_fieldMap_isIso (X : Scheme.{u}) [IsIntegral X] :
    IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.Scheme.genericMap X).toNormalization (Normalization.Scheme.toNormalization_genericPoint X)) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.Scheme.genericMap X).toNormalization
    (Normalization.Scheme.toNormalization_genericPoint X)).hom.toAlgebra
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
  rw [Support.Fields.genericFieldMap_finrank_eq_residueDegree]
  let : IsPreimmersion (Normalization.Scheme.genericMap X) := by unfold Normalization.Scheme.genericMap; infer_instance
  have h := CyclePushforward.residueDegree_comp (Normalization.Scheme.genericMap X).toNormalization
    (Normalization.Scheme.normalizationMap X) (genericPoint (Spec X.functionField))
  change ((Normalization.Scheme.genericMap X).toNormalization ≫ (Normalization.Scheme.genericMap X).fromNormalization).residueDegree _ = _ at h
  rw [Scheme.Hom.toNormalization_fromNormalization,
    Principal.ClosedSectionCycle.residueDegree_immersion] at h
  exact Nat.eq_one_of_dvd_one ⟨_, h.trans (Nat.mul_comm _ _)⟩

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

def intermediate : Scheme :=
  letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Relative.Normalization.relativeNormalization Y X.functionField

instance : IsIntegral (intermediate f hη) := by
  unfold intermediate
  infer_instance

def intermediateMap : intermediate f hη ⟶ Y :=
  letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Relative.Normalization.relativeNormalizationMap Y X.functionField

instance : IsIntegralHom (intermediateMap f hη) := by
  unfold intermediateMap intermediate
  infer_instance

def intermediateGenericMap : Spec X.functionField ⟶ intermediate f hη :=
  letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Relative.NormalizationFields.toRelativeNormalization Y X.functionField

theorem intermediateGenericMap_genericPoint :
    intermediateGenericMap f hη (genericPoint (Spec X.functionField)) =
      genericPoint (intermediate f hη) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  exact Relative.NormalizationFields.toRelativeNormalization_genericPoint Y X.functionField

def genericLift : Spec X.functionField ⟶ pullback f (intermediateMap f hη) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  exact pullback.lift (Normalization.Scheme.genericMap X) (Relative.NormalizationFields.toRelativeNormalization Y X.functionField) (by
    change Normalization.Scheme.genericMap X ≫ f = Relative.NormalizationFields.toRelativeNormalization Y X.functionField ≫
      Relative.Normalization.relativeNormalizationMap Y X.functionField
    rw [Relative.NormalizationFields.toRelativeNormalization_comp]
    exact (Normalization.Functor.genericMap_square f hη).symm)

def birationalFactor : Normalization.Scheme.normalization X ⟶ intermediate f hη :=
  (Normalization.Scheme.genericMap X).normalizationDesc (genericLift f hη)
    (pullback.fst f (intermediateMap f hη)) (by simp [genericLift]) ≫
      pullback.snd f (intermediateMap f hη)

theorem birationalFactor_comp :
    birationalFactor f hη ≫ intermediateMap f hη = Normalization.Scheme.normalizationMap X ≫ f := by
  rw [birationalFactor, Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.Hom.normalizationDesc_comp]
  rfl

theorem toNormalization_birationalFactor :
    (Normalization.Scheme.genericMap X).toNormalization ≫ birationalFactor f hη =
      intermediateGenericMap f hη := by
  rw [birationalFactor, ← Category.assoc, Scheme.Hom.toNormalization_normalizationDesc]
  exact pullback.lift_snd _ _ _

theorem birationalFactor_genericPoint :
    birationalFactor f hη (genericPoint (Normalization.Scheme.normalization X)) =
      genericPoint (intermediate f hη) := by
  rw [← Normalization.Scheme.toNormalization_genericPoint X]
  change ((Normalization.Scheme.genericMap X).toNormalization ≫ birationalFactor f hη) _ = _
  rw [toNormalization_birationalFactor]
  exact intermediateGenericMap_genericPoint f hη

theorem birationalFactor_isProper {k : Type u} [Field k] [CharZero k]
    (gX : X ⟶ Spec (.of k)) [LocallyOfFiniteType gX] [IsProper f] :
    IsProper (birationalFactor f hη) := by
  let : IsFinite (Normalization.Scheme.normalizationMap X) := Normalization.Scheme.normalizationMap_isFinite X gX
  let : IsProper (birationalFactor f hη ≫ intermediateMap f hη) := by
    rw [birationalFactor_comp]
    infer_instance
  exact IsProper.of_comp (birationalFactor f hη) (intermediateMap f hη)

theorem birationalFactor_fieldMap_isIso :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    Module.Finite Y.functionField X.functionField →
    IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (birationalFactor f hη) (birationalFactor_genericPoint f hη)) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  intro hfinite
  let := hfinite
  let := toNormalization_fieldMap_isIso X
  have h := Generic.Fields.genericFieldMap_comp (Normalization.Scheme.genericMap X).toNormalization
    (birationalFactor f hη) (Normalization.Scheme.toNormalization_genericPoint X) (birationalFactor_genericPoint f hη)
  have hc := Generic.Fields.genericFieldMap_congr (toNormalization_birationalFactor f hη)
    ((congrArg (birationalFactor f hη) (Normalization.Scheme.toNormalization_genericPoint X)).trans
      (birationalFactor_genericPoint f hη)) (intermediateGenericMap_genericPoint f hη)
  have hi : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (birationalFactor f hη) (birationalFactor_genericPoint f hη) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.Scheme.genericMap X).toNormalization (Normalization.Scheme.toNormalization_genericPoint X)) := by
    rw [← h, hc]
    exact Relative.NormalizationFields.toRelativeNormalization_fieldMap_isIso Y X.functionField
  exact IsIso.of_isIso_comp_right _ (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.Scheme.genericMap X).toNormalization
    (Normalization.Scheme.toNormalization_genericPoint X))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactor
