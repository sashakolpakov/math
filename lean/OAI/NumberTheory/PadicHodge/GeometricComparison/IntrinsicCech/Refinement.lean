import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Refinement

/-! # Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Refinement.CechRefinement

noncomputable section

/-! The actual refinement maps are natural in coefficients and lift to the native sheaf Čech resolution. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i))

theorem naturality {P Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X} (a : P ⟶ Q) :
    (IntrinsicCech.Functor.IntrinsicCechFunctor.functor R X U).map a ≫ Cech.Refinement.CechRefinement.map R X U V r hr Q =
      Cech.Refinement.CechRefinement.map R X U V r hr P ≫ (IntrinsicCech.Functor.IntrinsicCechFunctor.functor R X V).map a := by
  ext n : 1
  exact (((FormalCoproduct.evalOp X.Opens (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X)).map
    ((IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R X).map a)).naturality
      ((Cech.Refinement.CechRefinement.simplicialMap X U V r hr).app (op ⦋n⦌)).op).symm

def transformation : IntrinsicCech.Functor.IntrinsicCechFunctor.functor R X U ⟶ IntrinsicCech.Functor.IntrinsicCechFunctor.functor R X V where
  app P := Cech.Refinement.CechRefinement.map R X U V r hr P
  naturality _ _ a := CechRefinement.naturality R X U V r hr a

def sheafTransformation :
    IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X U ⟶ IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X V :=
  Functor.whiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (Functor.whiskerRight (transformation R X U V r hr)
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafification R X).mapHomologicalComplex (.up ℕ)))

theorem sheafAugmentation_naturality
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R X U).app F ≫
        (sheafTransformation R X U V r hr).app F =
      (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafAugmentation R X V).app F := by
  let S := (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafification R X).mapHomologicalComplex (.up ℕ)
  let e := (IntrinsicCech.Functor.IntrinsicCechFunctor.singleIso R X).hom.app F
  change (e ≫ S.map (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U F.obj)) ≫
      S.map (Cech.Refinement.CechRefinement.map R X U V r hr F.obj) = e ≫ S.map (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X V F.obj)
  exact (Category.assoc _ _ _).trans (congrArg (fun k => e ≫ k)
    ((S.map_comp _ _).symm.trans (congrArg S.map (Cech.Refinement.CechRefinement.augmentation_naturality R X U V r hr F.obj))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Refinement.CechRefinement
