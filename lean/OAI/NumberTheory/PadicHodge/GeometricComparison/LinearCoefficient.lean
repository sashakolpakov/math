import OAI.NumberTheory.PadicHodge.GeometricComparison.AcyclicCoefficient
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived

/-! # Linear Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LinearCoefficient.LinearCoefficientNaturality

noncomputable section

/-! Linear coefficient-object naturality for the native acyclic comparison. -/

open _root_.CategoryTheory Limits Abelian Opposite OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext

universe u v w z

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {A B : C} (v : A ⟶ B) (K : CochainComplex C ℤ)

def complexMap : AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) B K ⟶ AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K :=
  (((linearCoyoneda R C).map v.op).mapHomologicalComplex (.up ℤ)).app K

theorem forget_naturality (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) B K).homology n) :
    AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A K n
      (HomologicalComplex.homologyMap (complexMap R v K) n x) =
      HomologicalComplex.homologyMap (AcyclicCoefficient.AcyclicCoefficientNaturality.complexMap v K) n
        (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) B K n x) := by
  let G := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) n).map (complexMap R v K)
  exact congrArg (fun g => g x) (ShortComplex.mapHomologyIso_inv_naturality ψ G)

variable [HasExt.{w} C] [HasDerivedCategory.{z} C] [EnoughInjectives C]

theorem naturality (b : ℤ) [K.IsStrictlyGE b]
    (hA : ∀ p q, Subsingleton (Ext.{w} A (K.X p) (q + 1)))
    (hB : ∀ p q, Subsingleton (Ext.{w} B (K.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) B K).homology n) :
    AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) A K b hA n
      (HomologicalComplex.homologyMap (complexMap R v K) n x) =
      (DerivedCategory.singleFunctor C 0).map v ≫ AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) B K b hB n x :=
  (congrArg (AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hA n) (forget_naturality R v K n x)).trans
    (AcyclicCoefficient.AcyclicCoefficientNaturality.naturality v K b hA hB n (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) B K n x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LinearCoefficient.LinearCoefficientNaturality
