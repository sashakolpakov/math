import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge

/-! # Total Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison

noncomputable section

/-!
# Additive functors commute with nonnegative total complexes

Each total degree uses only finitely many bidegrees. Preservation of
these finite coproducts follows from additivity.
-/

open _root_.CategoryTheory Limits

instance finiteBidegrees (n : ℕ) : Finite
    {i : ℕ × ℕ // ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) i = n} := by
  let f : {i : ℕ × ℕ // ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) i = n} → Fin (n + 1) := fun i =>
    ⟨i.val.1, by have h := i.property; change i.val.1 + i.val.2 = n at h; omega⟩
  apply Finite.of_injective f
  intro a b h
  have h₁ : a.val.1 = b.val.1 := congrArg Fin.val h
  have ha := a.property
  have hb := b.property
  change a.val.1 + a.val.2 = n at ha
  change b.val.1 + b.val.2 = n at hb
  apply Subtype.ext
  exact Prod.ext h₁ (by omega)

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  (G : C ⥤ D) [G.Additive]
  (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem component_isIso (n : ℕ) :
    IsIso (Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G K n) := by
  let J := (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
    (ComplexShape.up ℕ)) ⁻¹' {n}
  have : Finite J := finiteBidegrees n
  have : PreservesColimitsOfShape (Discrete J) G := inferInstance
  let f : J → C := K.toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) n
  have : HasCoproduct f := inferInstance
  have : HasCoproduct (fun j => G.obj (f j)) := inferInstance
  exact inferInstanceAs (IsIso (sigmaComparison G f))

def iso : (Comparison.Betti.TotalComplexFunctor.mapBicomplex G K).total (ComplexShape.up ℕ) ≅
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (K.total (ComplexShape.up ℕ)) := by
  have (n : ℕ) : IsIso ((Comparison.Betti.TotalComplexFunctor.totalComparison G K).f n) := component_isIso G K n
  have : IsIso (Comparison.Betti.TotalComplexFunctor.totalComparison G K) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact asIso (Comparison.Betti.TotalComplexFunctor.totalComparison G K)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison
