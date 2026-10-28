import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived

/-! # Linear Acyclic Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LinearAcyclicNaturality.LinearAcyclicComparison

noncomputable section

/-! Naturality of the proved linear acyclic-complex comparison for actual maps of complexes. -/

open _root_.CategoryTheory Abelian Limits Opposite OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {R : Type v} [CommRing R] [Linear R C] (A : C)
  {K L : CochainComplex C ℤ}

theorem forget_naturality (f : K ⟶ L) (n : ℤ)
    (a : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n) :
    AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A L n
      (HomologicalComplex.homologyMap
        ((((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℤ)).map f) n a) =
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map f) n
          (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A K n a) := by
  let F := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let H := (((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℤ)).map f
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) n).map H
  exact congrArg (fun g => g a) (ShortComplex.mapHomologyIso_inv_naturality φ F)

variable [EnoughInjectives C] [HasExt.{w} C] [HasDerivedCategory.{w'} C]
  (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]

theorem naturality
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A (L.X p) (q + 1)))
    (f : K ⟶ L) (n : ℤ)
    (a : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n) :
    AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) A L c hL n
      (HomologicalComplex.homologyMap
        ((((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℤ)).map f) n a) =
      AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) A K b hK n a ≫
        (DerivedCategory.Q.map f)⟦n⟧' := by
  change AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A L c hL n
    (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A L n _) = _
  rw [forget_naturality]
  exact AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality.Ext.acyclicHomCohomologyDerivedEquiv_naturality A K L b c hK hL f n
    (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A K n a)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LinearAcyclicNaturality.LinearAcyclicComparison
