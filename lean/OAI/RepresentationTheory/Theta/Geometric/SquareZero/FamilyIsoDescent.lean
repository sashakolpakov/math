import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Pair
import OAI.RepresentationTheory.Theta.Geometric.BaseChangeLineDescent

/-! # Family Iso Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.FamilyIsoDescent

noncomputable section

/-! The injected split square-zero parameter algebra has effective
descent for compatible native line-bundle isomorphisms on any flat family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

theorem squareZero_flat_family_iso_descent
    {V R S : Type} [AddCommGroup V] [Module ℂ V] [Module ℂᵐᵒᵖ V] [IsCentralScalar ℂ V]
    [CommRing R] [Algebra ℂ R] [Nontrivial R] [CommRing S] [Algebra ℂ S] [Nontrivial S]
    (i : V →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap)
    {Y Z : Scheme} (h : Y ⟶ Spec (.of (TrivSqZeroExt ℂ V))) [Flat h]
    (u : Z ⟶ Y) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (Subalgebra.squareZeroSubalgebraMap i hsq).toRingHom)))
    {L N : Y.Modules} (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (e : (Scheme.Modules.pullback u).obj L ≅ (Scheme.Modules.pullback u).obj N)
    (heq : AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.CompatibleHom u e.hom) :
    ∃! d : L ≅ N, (Scheme.Modules.pullback u).mapIso d = e := by
  let : Algebra (TrivSqZeroExt ℂ V) R := (Subalgebra.squareZeroSubalgebraMap i hsq).toAlgebra
  let : Algebra (TrivSqZeroExt ℂ V) (S ⊗[ℂ] S) :=
    (((Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S).comp q).comp
      (Subalgebra.squareZeroSubalgebraMap i hsq)).toAlgebra
  have hk : ∀ a, algebraMap (TrivSqZeroExt ℂ V) R a = Subalgebra.squareZeroSubalgebraMap i hsq a := fun _ => rfl
  have hp : ∀ a, algebraMap (TrivSqZeroExt ℂ V) (S ⊗[ℂ] S) a =
      (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S) (q (Subalgebra.squareZeroSubalgebraMap i hsq a)) :=
    fun _ => rfl
  exact BaseChangeLineDescent.flat_baseChange_lineIso_descent (Subalgebra.squareZeroSubalgebraMap_injective i hi hsq)
    (Pair.squareZeroFirstQuotientHom i hsq q hk hp) (Pair.squareZeroSecondQuotientHom i hsq q he hk hp)
    (Pair.squareZero_quotient_pair_exact i hsq q he hk hp) h u v H hL hN e heq

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.FamilyIsoDescent
