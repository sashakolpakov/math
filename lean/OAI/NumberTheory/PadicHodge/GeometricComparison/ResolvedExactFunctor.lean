import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearExact
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoExactFunctor

/-! # Resolved Exact Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedExactFunctor.ResolvedExactFunctorComparison

noncomputable section

/-! Actual acyclic resolution comparisons commute with an exact functor and a commuting geometric square. -/

open _root_.CategoryTheory Limits Abelian

universe u u' v w w' z z'

variable (R : Type v) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{z} C] [Linear R C] (A : C)

def equiv {K K' : CochainComplex C ℤ} (f : K ⟶ K') [QuasiIso f]
    (b : ℤ) [K'.IsStrictlyGE b]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K'.X p) (q + 1))) (n : ℤ) :
    (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K').homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) A K' b hK n).trans (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n)

variable {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D]
  [HasExt.{w'} D] [HasDerivedCategory.{z'} D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem naturality {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g]
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : (F.mapHomologicalComplex (.up ℤ)).map f ≫ b = a ≫ g)
    (c d : ℤ) [K'.IsStrictlyGE c] [L'.IsStrictlyGE d]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K'.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{w'} (F.obj A) (L'.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K').homology n) :
    equiv R (F.obj A) g d hL n (HomologicalComplex.homologyMap (LinearExact.LinearExactFunctorNaturality.complexMap R F A b) n x) =
      AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n (equiv R A f c hK n x) :=
  (congrArg (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R (F.obj A) g n)
    (LinearExact.LinearExactFunctorNaturality.naturality R F A b c d hK hL n x)).trans
      (QuasiIsoExactFunctor.DerivedQuasiIsoExactFunctor.naturality R F A f g a b h n
        (AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) A K' c hK n x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedExactFunctor.ResolvedExactFunctorComparison
