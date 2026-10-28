import OAI.NumberTheory.PadicHodge.GeometricComparison.AcyclicExact
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived

/-! # Linear Exact -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LinearExact.LinearExactFunctorNaturality

noncomputable section

/-! Linear exact-functor naturality of the actual acyclic derived comparison. -/

open _root_.CategoryTheory Limits Abelian Opposite OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext

universe u u' v w w' z z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory.{z} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [HasExt.{w'} D] [HasDerivedCategory.{z'} D]
  (R : Type v) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R] (A : C)
  {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
  (φ : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)

def complexMap : AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K ⟶ AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) (F.obj A) L where
  f n := ModuleCat.ofHom ((Linear.rightComp R (F.obj A) (φ.f n)).comp
    (F.mapLinearMap R (X := A) (Y := K.X n)))
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (F.map a ≫ φ.f n) ≫ L.d n m = F.map (a ≫ K.d n m) ≫ φ.f m
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map a ≫ k) (φ.comm n m)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ φ.f m) (F.map_comp a (K.d n m)).symm)))

omit [HasExt C] [HasDerivedCategory C] [HasExt D] [HasDerivedCategory D] in
theorem forget_naturality (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n) :
    AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) (F.obj A) L n
      (HomologicalComplex.homologyMap (complexMap R F A φ) n x) =
      HomologicalComplex.homologyMap (AcyclicExact.AcyclicExactFunctorNaturality.complexMap F A φ) n
        (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A K n x) := by
  let G := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) n).map (complexMap R F A φ)
  exact congrArg (fun g => g x) (ShortComplex.mapHomologyIso_inv_naturality ψ G)

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F] [EnoughInjectives C] [EnoughInjectives D]

theorem naturality (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{w'} (F.obj A) (L.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n) :
    AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) (F.obj A) L c hL n
      (HomologicalComplex.homologyMap (complexMap R F A φ) n x) =
      AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A φ n
        (AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (R := R) A K b hK n x) :=
  (congrArg (AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv (F.obj A) L c hL n) (forget_naturality R F A φ n x)).trans
    (AcyclicExact.AcyclicExactFunctorNaturality.naturality F A φ b c hK hL n
      (AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A K n x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LinearExact.LinearExactFunctorNaturality
