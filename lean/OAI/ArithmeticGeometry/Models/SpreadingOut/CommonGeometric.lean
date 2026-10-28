import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenModel

/-! # Common Geometric -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.CommonGeometric.Construction

noncomputable section

/-! A finite family of models with geometrically irreducible fibers admits
a common coefficient ring with all its geometric properties retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v

theorem finite_geometric_models_common_base
    {K : Type u} [Field K] [NumberField K] {ι : Type v} [Finite ι]
    (X : ι → Over (Spec (.of K))) (M : ∀ i, Foundations.Constructions.CoefficientModel K (X i))
    (hM : ∀ i, Smooth (M i).model.hom ∧ IsProper (M i).model.hom ∧
      GeometricallyIrreducible (M i).model.hom) :
    ∃ (s : Finset K) (N : ι → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
      (_e : ∀ i, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (N i) ≅ X i),
      ∀ i, Smooth (N i).hom ∧ IsProper (N i).hom ∧ GeometricallyIrreducible (N i).hom := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let s := Finset.univ.biUnion (fun i ↦ (M i).coefficients)
  have h (i : ι) : (M i).coefficients ⊆ s :=
    Finset.subset_biUnion_of_mem (fun i ↦ (M i).coefficients) (Finset.mem_univ i)
  let N (i : ι) := (M i).enlarge s (h i)
  refine ⟨s, (fun i ↦ (N i).model), (fun i ↦ (N i).genericIso), fun i ↦ ?_⟩
  have : Smooth (M i).model.hom := (hM i).1
  have : IsProper (M i).model.hom := (hM i).2.1
  have : GeometricallyIrreducible (M i).model.hom := (hM i).2.2
  exact ⟨OpenModel.Construction.coefficient_enlarge_smooth (M i) s (h i),
    OpenModel.Construction.coefficient_enlarge_proper (M i) s (h i),
    OpenModel.Construction.coefficient_enlarge_geometricallyIrreducible (M i) s (h i)⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.CommonGeometric.Construction
