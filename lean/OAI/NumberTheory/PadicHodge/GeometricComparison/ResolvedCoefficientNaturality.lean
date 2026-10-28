import OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedExactFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearCoefficient

/-! # Resolved Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedCoefficientNaturality.ResolvedExactFunctorComparison

noncomputable section

/-! Changing the native coefficient object commutes with the actual resolution comparison. -/

open _root_.CategoryTheory Limits Abelian

universe u v w z

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{z} C] [Linear R C]
  {A B : C} (v : A ⟶ B) {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]

omit [EnoughInjectives C] [HasExt C] in
theorem quasiIso_coefficient (n : ℤ)
    (x : (DerivedCategory.singleFunctor C 0).obj B ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n ((DerivedCategory.singleFunctor C 0).map v ≫ x) =
      (DerivedCategory.singleFunctor C 0).map v ≫ DerivedQuasiHom.DerivedQuasiIsoHom.equiv R B f n x := by
  rw [QuasiIsoExactFunctor.DerivedQuasiIsoExactFunctor.equiv_apply, QuasiIsoExactFunctor.DerivedQuasiIsoExactFunctor.equiv_apply]
  exact Category.assoc _ _ _

theorem coefficient_naturality (b : ℤ) [L.IsStrictlyGE b]
    (hA : ∀ p q, Subsingleton (Ext.{w} A (L.X p) (q + 1)))
    (hB : ∀ p q, Subsingleton (Ext.{w} B (L.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) B L).homology n) :
    ResolvedExactFunctor.ResolvedExactFunctorComparison.equiv R A f b hA n (HomologicalComplex.homologyMap (LinearCoefficient.LinearCoefficientNaturality.complexMap R v L) n x) =
      (DerivedCategory.singleFunctor C 0).map v ≫ ResolvedExactFunctor.ResolvedExactFunctorComparison.equiv R B f b hB n x :=
  (congrArg (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n) (LinearCoefficient.LinearCoefficientNaturality.naturality R v L b hA hB n x)).trans
    (quasiIso_coefficient R v f n (AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) B L b hB n x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedCoefficientNaturality.ResolvedExactFunctorComparison
