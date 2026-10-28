import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackNormalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalSection

/-! # Pullback Normalization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackNormalization.IntrinsicCechPullback

noncomputable section

/-! The actual native integer Čech pullback is induced by its explicit bicomplex pullback. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := Instances.IntrinsicCechInstances.hasCoproducts R X.left
local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := Instances.IntrinsicCechInstances.hasCoproducts R Y.left
local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).Additive := Instances.IntrinsicCechInstances.additive R Y.left U
local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).Additive := Instances.IntrinsicCechInstances.additive R X.left V

def bicomplexMap {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (DeRham.Int.inverseImage f) (Bicomplex.IntrinsicCechBicomplex.bicomplex R Y.left U K) ⟶
      Bicomplex.IntrinsicCechBicomplex.bicomplex R X.left V L :=
  Functor.ResolutionPullbackTotal.FunctorResolutionPullbackTotal.bicomplexMap (DeRham.Int.inverseImage f)
    (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U) (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V)
    (CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr) K ≫
      ((Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).mapHomologicalComplex (.up ℕ)).map b

theorem integerMap_eq {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    PullbackTotal.IntrinsicCechPullback.integerMap f U V r hr b =
      TotalSection.TotalSectionPullbackNaturality.resolvedMap (DeRham.Int.inverseImage f) (bicomplexMap f U V r hr b) := by
  let α := Functor.ResolutionPullbackTotal.FunctorResolutionPullbackTotal.bicomplexMap (DeRham.Int.inverseImage f)
    (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U) (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V)
    (CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr) K
  let β := ((Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).mapHomologicalComplex (.up ℕ)).map b
  let I := TotalFinite.IntegerTotalFunctor.functor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)
  have h := Functor.ResolutionPullbackNormalization.FunctorResolutionPullbackTotal.integerMap_eq (DeRham.Int.inverseImage f)
    (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U) (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V)
    (CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr) K
  exact (congrArg (fun k => k ≫ I.map β) h).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun k => (Finite.TotalIso.FiniteTotalExtension.iso (DeRham.Int.inverseImage f)
        (Bicomplex.IntrinsicCechBicomplex.bicomplex R Y.left U K)).inv ≫ k) (I.map_comp α β).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackNormalization.IntrinsicCechPullback
