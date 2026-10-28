import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleAssociativity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSchemeSolution

/-! # Scheme Cocycle Splitting -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleSplitting

noncomputable section

/-! A natural symmetric regular cocycle on a finite commutative group scheme has a regular splitting. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CocycleSchemeValues

variable (k R : Type u) [Field k] [IsAlgClosed k] [CommRing R] [HopfAlgebra k R]
  [Coalgebra.IsCocomm k R] [Module.Finite k R]
  (C : NaturalSchemeCocycle.NaturalCocycle ((Spec (.of R)).asOver (Spec (.of k))))

/-- The splitting is an actual coordinate unit, and its identities hold on all test schemes. -/
theorem exists_regular_splitting :
    ∃ a : Rˣ,
      (∀ T : Over (Spec (.of k)),
        PoincareBundle.Finite.CocycleSchemeValues.solution k R a T (1 : T ⟶ (Spec (.of R)).asOver (Spec (.of k))) = 1) ∧
      ∀ (T : Over (Spec (.of k))) (x y : T ⟶ (Spec (.of R)).asOver (Spec (.of k))),
        C.value x y * PoincareBundle.Finite.CocycleSchemeValues.solution k R a T (x * y) = PoincareBundle.Finite.CocycleSchemeValues.solution k R a T x * PoincareBundle.Finite.CocycleSchemeValues.solution k R a T y := by
  have : Nontrivial R := (Bialgebra.counitAlgHom k R).toRingHom.domain_nontrivial
  let c := SchemeCocycleRecovery.coordinate k R C
  have hc : Symmetric.CocycleCoalgebra.IsNormalizedSymmetricCocycle k R (c : R ⊗[k] R) :=
    AlgebraCocycleAssociativity.normalizedSymmetricCocycle k R
      (SchemeCocycleCoordinates.algebraCocycle k R C)
  obtain ⟨a, hε, hΔ⟩ := PoincareBundle.Finite.SymmetricCocycle.exists_unit_solution k R c hc
  refine ⟨a, CocycleSchemeSolution.solution_one k R a hε, ?_⟩
  intro T x y
  have h := CocycleSchemeSolution.solution_mul k R c a hΔ T x y
  have hv := SchemeCocycleRecovery.value_eq k R C T x y
  exact (congrArg (fun v => v * PoincareBundle.Finite.CocycleSchemeValues.solution k R a T (x * y)) hv).symm.trans h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleSplitting
