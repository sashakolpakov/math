import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Base Ring Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.BaseRingMap.FormsBaseChange

noncomputable section

/-! Changing the base ring induces the canonical quotient map on actual differential forms in every degree. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

def baseRelation {n : ℕ} : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n → AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex S A n
  | .add v i x y => .add v i x y
  | .mul v i x y => .mul v i x y
  | .base v i r => .base v i (algebraMap R S r)
  | .alt v i j hij hne => .alt v i j hij hne

theorem relation_baseRelation {n : ℕ} (r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation R A n r = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation S A n (baseRelation R S A r) := by
  cases r with
  | base v i r =>
    change Finsupp.single (Function.update v i (algebraMap R A r)) 1 =
      Finsupp.single (Function.update v i (algebraMap S A (algebraMap R S r))) 1
    rw [IsScalarTower.algebraMap_apply R S A]
  | add => rfl
  | mul => rfl
  | alt => rfl

theorem base_relations_le (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n ≤ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  rw [relation_baseRelation R S A r]
  exact Submodule.subset_span (Set.mem_range_self _)

def formBaseMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A n :=
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).liftQ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n).mkQ
    (fun _ hx => Submodule.Quotient.mk_eq_zero _ |>.mpr (base_relations_le R S A n hx))

theorem formBaseMap_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    formBaseMap R S A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A a v := rfl

theorem formBaseMap_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formBaseMap R S A (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (formBaseMap R S A n ω) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v a =>
    change formBaseMap R S A (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (formBaseMap R S A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol, formBaseMap_symbol]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.BaseRingMap.FormsBaseChange
