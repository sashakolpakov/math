import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionPostcomp

/-! # Pullback Adjoint -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackAdjoint.IntrinsicCechPullback

noncomputable section

/-! The constructed refined Čech pullback has the actual direct-image Čech map as its adjoint. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

theorem adjoint_refined (P : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) (Q : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)
    (a : (DeRham.Int.inverseImage f).obj P ⟶ Q) :
    (DeRham.Int.imageComplexAdjunction f).homEquiv _ _
        ((CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr).app P ≫ (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).map a) =
      (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).map ((DeRham.Int.imageAdjunction f).homEquiv P Q a) ≫
        (Image.IntrinsicCechImage.iso f U Q).hom ≫
          ((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).map
            ((Refinement.CechRefinement.sheafTransformation R X.left (fun i => f.left ⁻¹ᵁ U i) V r hr).app Q) := by
  let N := Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i)
  let M := Functor.IntrinsicCechFunctor.sheafFunctor R X.left V
  let m := (CechPullback.IntrinsicCechPullback.transformation f U).app P
  let t := Refinement.CechRefinement.sheafTransformation R X.left (fun i => f.left ⁻¹ᵁ U i) V r hr
  let A := DeRham.Int.imageComplexAdjunction f
  let G := (DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)
  have hs : (m ≫ t.app ((DeRham.Int.inverseImage f).obj P)) ≫ M.map a = (m ≫ N.map a) ≫ t.app Q :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => m ≫ k) (t.naturality a).symm).trans
      (Category.assoc _ _ _).symm)
  have hm := AdjunctionResolutionPostcomp.AdjunctionResolutionPullback.map_postcomp (DeRham.Int.imageAdjunction f)
    (Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U) N (ImageNaturality.IntrinsicCechImage.functorIso f U) P Q a
  exact (congrArg (A.homEquiv _ _) hs).trans
    ((A.homEquiv_naturality_right (m ≫ N.map a) (t.app Q)).trans
      ((congrArg (fun k => k ≫ G.map (t.app Q)) hm).trans (Category.assoc _ _ _)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackAdjoint.IntrinsicCechPullback
