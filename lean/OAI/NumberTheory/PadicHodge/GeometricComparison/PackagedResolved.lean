import OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalDerived

/-! # Packaged Resolved -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PackagedResolved.PackagedResolvedComparison

noncomputable section

/-! The packaged native comparison system retains exact-functor and coefficient naturality. -/

open _root_.CategoryTheory Limits Abelian

universe u u' v w w' z z'

variable (R : Type v) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{z} C] [Linear R C]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D]
  [HasExt.{w'} D] [HasDerivedCategory.{z'} D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : C) (B : D) (e : F.obj A ≅ B)

def equivWithSystem (A : C) (P : NaturalDerived.NaturalDerivedComparison.System (R := R) A)
    {K K' : CochainComplex C ℤ} (f : K ⟶ K') [QuasiIso f]
    (c : ℤ) [K'.IsStrictlyGE c]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K'.X p) (q + 1))) (n : ℤ) :
    (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K').homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (P.equiv K' c hK n).trans (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n)

def equiv (A : C) {K K' : CochainComplex C ℤ} (f : K ⟶ K') [QuasiIso f]
    (c : ℤ) [K'.IsStrictlyGE c]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K'.X p) (q + 1))) (n : ℤ) :
    (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K').homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  ((NaturalDerived.NaturalDerivedComparison.constructed (R := R) A).equiv K' c hK n).trans
    (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n)

theorem with_coefficient {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g]
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : (F.mapHomologicalComplex (.up ℤ)).map f ≫ b = a ≫ g)
    (c d : ℤ) [K'.IsStrictlyGE c] [L'.IsStrictlyGE d]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K'.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{w'} B (L'.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K').homology n) :
    PackagedResolvedComparison.equiv R B g d hL n (HomologicalComplex.homologyMap
      (LinearExact.LinearExactFunctorNaturality.complexMap R F A b ≫ LinearCoefficient.LinearCoefficientNaturality.complexMap R e.inv L') n x) =
      (DerivedCategory.singleFunctor D 0).map e.inv ≫
        AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n (PackagedResolvedComparison.equiv R A f c hK n x) :=
  ResolvedCoefficient.ResolvedExactFunctorComparison.with_coefficient R F A B e f g a b h c d hK hL n x

theorem with_coefficient_of_system_eq
    (P : NaturalDerived.NaturalDerivedComparison.System (R := R) A)
    (Q : NaturalDerived.NaturalDerivedComparison.System (R := R) B)
    (hP : P = NaturalDerived.NaturalDerivedComparison.constructed A)
    (hQ : Q = NaturalDerived.NaturalDerivedComparison.constructed B)
    {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g]
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : (F.mapHomologicalComplex (.up ℤ)).map f ≫ b = a ≫ g)
    (c d : ℤ) [K'.IsStrictlyGE c] [L'.IsStrictlyGE d]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K'.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{w'} B (L'.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K').homology n) :
    equivWithSystem R B Q g d hL n (HomologicalComplex.homologyMap
      (LinearExact.LinearExactFunctorNaturality.complexMap R F A b ≫ LinearCoefficient.LinearCoefficientNaturality.complexMap R e.inv L') n x) =
      (DerivedCategory.singleFunctor D 0).map e.inv ≫
        AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n
          (equivWithSystem R A P f c hK n x) := by
  subst P Q
  exact with_coefficient R F A B e f g a b h c d hK hL n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PackagedResolved.PackagedResolvedComparison
