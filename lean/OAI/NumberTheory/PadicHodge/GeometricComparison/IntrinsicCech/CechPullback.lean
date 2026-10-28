import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ImageAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Refinement

/-! # Cech Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechPullback.IntrinsicCechPullback

noncomputable section

/-! Actual geometric inverse image acts on the native Čech resolution, including arbitrary cover refinements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι : Type} (U : ι → Y.left.Opens)

def transformation : IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U ⋙
      (DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ) ⟶
    DeRham.Int.inverseImage f ⋙ IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i) :=
  AdjunctionResolutionTransformation.AdjunctionResolutionPullback.transformation (DeRham.Int.imageAdjunction f)
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U)
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i))
    (ImageNaturality.IntrinsicCechImage.functorIso f U)

theorem augmentation (P : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) :
    ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).map
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R Y.left U).app P) ≫ (transformation f U).app P =
      (HomologicalComplex.singleMapHomologicalComplex (DeRham.Int.inverseImage f) (.up ℕ) 0).hom.app P ≫
        (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R X.left (fun i => f.left ⁻¹ᵁ U i)).app
          ((DeRham.Int.inverseImage f).obj P) :=
  AdjunctionResolutionAugmentation.AdjunctionResolutionPullback.augmentation (DeRham.Int.imageAdjunction f)
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U)
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i))
    (ImageNaturality.IntrinsicCechImage.functorIso f U)
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R Y.left U)
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R X.left (fun i => f.left ⁻¹ᵁ U i))
    (ImageAugmentation.IntrinsicCechImage.augmentation f U) P

variable {κ : Type} (V : κ → X.left.Opens) (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

def refinedTransformation : IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U ⋙
      (DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ) ⟶
    DeRham.Int.inverseImage f ⋙ IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left V :=
  transformation f U ≫ Functor.whiskerLeft (DeRham.Int.inverseImage f)
    (Refinement.CechRefinement.sheafTransformation R X.left (fun i => f.left ⁻¹ᵁ U i) V r hr)

theorem refined_augmentation (P : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) :
    ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).map
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R Y.left U).app P) ≫
      (refinedTransformation f U V r hr).app P =
    (HomologicalComplex.singleMapHomologicalComplex (DeRham.Int.inverseImage f) (.up ℕ) 0).hom.app P ≫
      (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R X.left V).app ((DeRham.Int.inverseImage f).obj P) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (Refinement.CechRefinement.sheafTransformation R X.left
      (fun i => f.left ⁻¹ᵁ U i) V r hr).app ((DeRham.Int.inverseImage f).obj P)) (augmentation f U P)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => (HomologicalComplex.singleMapHomologicalComplex
            (DeRham.Int.inverseImage f) (.up ℕ) 0).hom.app P ≫ k)
              (Refinement.CechRefinement.sheafAugmentation_naturality R X.left
                (fun i => f.left ⁻¹ᵁ U i) V r hr ((DeRham.Int.inverseImage f).obj P)))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechPullback.IntrinsicCechPullback
