import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor

/-! # Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Refinement.CechRefinement

noncomputable section

/-! Actual refinement of covering families acts on Čech cochains and preserves the canonical augmentation. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial _root_.AlgebraicTopology

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i))

def coverMap : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U where
  f := r
  φ i := homOfLE (hr i)

def simplicialMap : (FormalCoproduct.mk κ V).cech ⟶ (FormalCoproduct.mk ι U).cech :=
  FormalCoproduct.cechFunctor.map (coverMap X U V r hr)

def cosimplicialMap (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.cosimplicial R X U P ⟶ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.cosimplicial R X V P :=
  Functor.whiskerRight (simplicialMap X U V r hr).rightOp
    ((FormalCoproduct.evalOp X.Opens (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P))

def map (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U P ⟶ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X V P :=
  (alternatingCofaceMapComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X)).map
    (cosimplicialMap R X U V r hr P)

theorem restriction_naturality (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) (n : SimplexCategory) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R X U P).app n ≫ (cosimplicialMap R X U V r hr P).app n =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R X V P).app n := by
  let E := (FormalCoproduct.mk ι U).cech.obj (op n)
  let D := (FormalCoproduct.mk κ V).cech.obj (op n)
  let a : D ⟶ E := (simplicialMap X U V r hr).app (op n)
  change Pi.lift (fun j : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (E.obj j)) ≫
      Pi.lift (fun i : D.I => Pi.π (fun j : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X P (E.obj j)) (a.f i) ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P).map (a.φ i).op) =
    Pi.lift (fun i : D.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (D.obj i))
  apply Pi.hom_ext
  intro i
  let M := fun j : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X P (E.obj j)
  let N := fun j : D.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X P (D.obj j)
  exact (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.pi_lift_comp_lift_projection M N
    (fun j => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (E.obj j)) a.f
    (fun j => (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P).map (a.φ j).op) i).trans
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection_map R X P (a.φ i)).symm.trans
        (Pi.lift_comp_π (fun j : D.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (D.obj j)) i).symm)

theorem augmentation_naturality (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U P ≫ CechRefinement.map R X U V r hr P =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X V P := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, AlgebraicGeometry.Crystalline.Cohomology.Cech.Augmentation.CechAugmentation.augmentation_f_zero]
  exact restriction_naturality R X U V r hr P ⦋0⦌

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Refinement.CechRefinement
