import OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedCoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientExt

/-! # Resolved Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedCoefficient.ResolvedExactFunctorComparison

noncomputable section

/-! Exact-functor resolution naturality with the actual target coefficient identification. -/

open _root_.CategoryTheory Limits Abelian

universe u u' v w w' z z'

variable (R : Type v) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{z} C] [Linear R C]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D]
  [HasExt.{w'} D] [HasDerivedCategory.{z'} D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : C) (B : D) (e : F.obj A ≅ B)

theorem with_coefficient {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g]
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : (F.mapHomologicalComplex (.up ℤ)).map f ≫ b = a ≫ g)
    (c d : ℤ) [K'.IsStrictlyGE c] [L'.IsStrictlyGE d]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K'.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{w'} B (L'.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K').homology n) :
    ResolvedExactFunctor.ResolvedExactFunctorComparison.equiv R B g d hL n (HomologicalComplex.homologyMap
      (LinearExact.LinearExactFunctorNaturality.complexMap R F A b ≫ LinearCoefficient.LinearCoefficientNaturality.complexMap R e.inv L') n x) =
      (DerivedCategory.singleFunctor D 0).map e.inv ≫
        AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n (ResolvedExactFunctor.ResolvedExactFunctorComparison.equiv R A f c hK n x) := by
  have hF (p q) : Subsingleton (Ext.{w'} (F.obj A) (L'.X p) (q + 1)) := by
    let := hL p q
    exact CoefficientExt.CoefficientExtIso.subsingleton e (L'.X p) (q + 1)
  let φ := LinearExact.LinearExactFunctorNaturality.complexMap R F A b
  let ψ := LinearCoefficient.LinearCoefficientNaturality.complexMap R e.inv L'
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) n
  have hc := congrArg (fun k => k x) (H.map_comp φ ψ)
  exact (congrArg (ResolvedExactFunctor.ResolvedExactFunctorComparison.equiv R B g d hL n) hc).trans
    ((ResolvedCoefficientNaturality.ResolvedExactFunctorComparison.coefficient_naturality R e.inv g d hL hF n (HomologicalComplex.homologyMap φ n x)).trans
      (congrArg (fun k => (DerivedCategory.singleFunctor D 0).map e.inv ≫ k)
        (ResolvedExactFunctor.ResolvedExactFunctorComparison.naturality R A F f g a b h c d hK hF n x)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedCoefficient.ResolvedExactFunctorComparison
