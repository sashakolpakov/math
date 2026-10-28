import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Generic Fiber -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.GenericFiber.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S T : Scheme} [IsIntegral S] [IsIntegral T]
variable {K : Type} [Field K]

/-- A dominant dimension-preserving morphism between integral varieties
has only the source generic point above the target generic point. -/
theorem genericFiber_eq_singleton (i : S ⟶ T) (g : T ⟶ Spec (.of K))
    [LocallyOfFiniteType i] [LocallyOfFiniteType g]
    (hη : i (genericPoint S) = genericPoint T)
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    i ⁻¹' {genericPoint T} = {genericPoint S} := by
  ext x
  change i x = genericPoint T ↔ x = genericPoint S
  constructor
  · intro hx
    by_contra hne
    let W : IrreducibleCloseds S := irreducibleSetEquivPoints.symm x
    let U : IrreducibleCloseds S :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
    have hW : W < U := by
      apply lt_of_le_not_ge (Set.subset_univ _)
      intro hUW
      have heq : (W : Set S) = Set.univ := Set.eq_univ_of_univ_subset hUW
      have hg : IsGenericPoint x (W : Set S) := by rfl
      rw [heq] at hg
      exact hne (hg.eq (genericPoint_spec S))
    have hηW : (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) =
        genericPoint T := by
      change i (CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) = _
      rw [CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq]
      change i (irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm x)) = _
      rw [OrderIso.apply_symm_apply]
      exact hx
    have hlow := FunctionFields.Construction.dimension_le_of_genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) hηW g
    rw [Category.assoc] at hlow
    change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ g) at hlow
    have hstrict := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt W U (i ≫ g) hW
    have hbound := Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le U (i ≫ g)
    omega
  · rintro rfl
    exact hη

/-- Properness extends finiteness of the generic fiber to an actual
Zariski-open neighborhood of the generic point of the target. -/
theorem exists_finite_neighborhood_of_generic (i : S ⟶ T) (g : T ⟶ Spec (.of K))
    [IsProper i] [LocallyOfFiniteType g]
    (hη : i (genericPoint S) = genericPoint T)
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    ∃ U : T.Opens, genericPoint T ∈ U ∧ IsFinite (i ∣_ U) := by
  apply exists_isFinite_morphismRestrict_of_finite_preimage_singleton i (genericPoint T)
  rw [genericFiber_eq_singleton i g hη hdim]
  exact Set.finite_singleton _

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.GenericFiber.Construction
