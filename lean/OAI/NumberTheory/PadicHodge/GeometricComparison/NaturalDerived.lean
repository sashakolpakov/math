import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearAcyclicNaturality

/-! # Natural Derived -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalDerived.NaturalDerivedComparison

noncomputable section

/-! The generic acyclic-complex equivalences and their naturality form one proved comparison system. -/

open _root_.CategoryTheory Abelian Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]
  {R : Type v} [CommRing R] [Linear R C] (A : C)

structure System where
  equiv (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K.X p) (q + 1))) (n : ℤ) :
    (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧)
  naturality {K L : CochainComplex C ℤ} (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{w} A (L.X p) (q + 1)))
    (f : K ⟶ L) (n : ℤ) (a : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n) :
    equiv L c hL n (HomologicalComplex.homologyMap
      ((((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℤ)).map f) n a) =
      equiv K b hK n a ≫ (DerivedCategory.Q.map f)⟦n⟧'

def constructed : System (R := R) A where
  equiv := by
    intro K b _ hK n
    exact AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) A K b hK n
  naturality := by
    intro K L b c _ _ hK hL f n a
    exact LinearAcyclicNaturality.LinearAcyclicComparison.naturality A b c hK hL f n a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalDerived.NaturalDerivedComparison
