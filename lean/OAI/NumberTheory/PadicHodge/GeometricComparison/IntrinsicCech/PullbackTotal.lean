import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackInteger
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Terms

/-! # Pullback Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackTotal.IntrinsicCechPullback

noncomputable section

/-! An actual geometric pullback and cover refinement induce an augmentation-compatible map of native integer Čech resolutions. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := Instances.IntrinsicCechInstances.hasCoproducts R X.left
local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := Instances.IntrinsicCechInstances.hasCoproducts R Y.left
local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).Additive := Instances.IntrinsicCechInstances.additive R Y.left U
local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).Additive := Instances.IntrinsicCechInstances.additive R X.left V

theorem refined_augmentation_zero (P : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) :
    (DeRham.Int.inverseImage f).map (((Functor.IntrinsicCechFunctor.sheafAugmentation R Y.left U).app P).f 0) ≫
        ((CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr).app P).f 0 =
      ((Functor.IntrinsicCechFunctor.sheafAugmentation R X.left V).app ((DeRham.Int.inverseImage f).obj P)).f 0 :=
  (congrArg (fun k => k.f 0) (CechPullback.IntrinsicCechPullback.refined_augmentation f U V r hr P)).trans (Category.id_comp _)

def integerMap {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj (Resolution.IntrinsicCechResolution.integerTotal R Y.left U K) ⟶
      Resolution.IntrinsicCechResolution.integerTotal R X.left V L :=
  Functor.ResolutionPullbackInteger.FunctorResolutionPullbackTotal.integerMap (DeRham.Int.inverseImage f)
    (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U) (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V)
    (CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr) K ≫ Terms.IntrinsicCechComparison.totalMap R X.left V b

theorem integerAugmentation {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).map (Resolution.IntrinsicCechResolution.integerEdge R Y.left U K) ≫
        integerMap f U V r hr b =
      ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (DeRham.Int.inverseImage f) ComplexShape.embeddingUpNat K).hom ≫
        HomologicalComplex.extendMap b ComplexShape.embeddingUpNat) ≫ Resolution.IntrinsicCechResolution.integerEdge R X.left V L := by
  have h₁ := Functor.ResolutionPullbackInteger.FunctorResolutionPullbackTotal.integerAugmentation (DeRham.Int.inverseImage f)
    (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U) (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V)
    (CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R Y.left U) (Functor.IntrinsicCechFunctor.sheafAugmentation R X.left V)
    (refined_augmentation_zero f U V r hr) K
  have h₂ := Terms.IntrinsicCechComparison.edge_naturality R X.left V b
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackTotal.IntrinsicCechPullback
