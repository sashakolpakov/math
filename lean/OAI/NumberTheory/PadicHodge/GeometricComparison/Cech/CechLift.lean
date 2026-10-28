import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Cech Lift -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechLift

noncomputable section

/-! Local preimages on a cover assemble into an actual zero-cochain whose image is the canonical Čech augmentation. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens)

local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι U)

def singleProjection (t : Fin 1 → ι) : ((N).obj (op ⦋0⦌)).obj t ⟶ U (t 0) :=
  Pi.π (U ∘ t) 0

def component (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.Presheaves R X)
    (z : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).obj P).X 0) (t : Fin 1 → ι) :
    P.obj (op (((N).obj (op ⦋0⦌)).obj t)) :=
  (Pi.π (fun a : ((N).obj (op ⦋0⦌)).I => P.obj (op (((N).obj (op ⦋0⦌)).obj a))) t) z

def assemble (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.Presheaves R X) (y : ∀ i, P.obj (op (U i))) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).obj P).X 0 :=
  (ModuleCat.piIsoPi (fun t : ((N).obj (op ⦋0⦌)).I =>
    P.obj (op (((N).obj (op ⦋0⦌)).obj t)))).inv
      (fun t => P.map (singleProjection R X U t).op (y (t 0)))

theorem component_assemble (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.Presheaves R X) (y : ∀ i, P.obj (op (U i)))
    (t : Fin 1 → ι) : component R X U P (assemble R X U P y) t =
      P.map (singleProjection R X U t).op (y (t 0)) :=
  congrArg (fun f => f (fun a => P.map (singleProjection R X U a).op (y (a 0))))
    (ModuleCat.piIsoPi_inv_kernel_ι
      (fun a : ((N).obj (op ⦋0⦌)).I => P.obj (op (((N).obj (op ⦋0⦌)).obj a))) t)

theorem map_component {P Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.Presheaves R X} (φ : P ⟶ Q)
    (z : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).obj P).X 0) (t : Fin 1 → ι) :
    component R X U Q (((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).map φ).f 0 z) t =
      φ.app _ (component R X U P z t) :=
  congrArg (fun f => f z) (Pi.map_π
    (fun a : ((N).obj (op ⦋0⦌)).I => φ.app (op (((N).obj (op ⦋0⦌)).obj a))) t)

theorem augmentation_f_zero (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.Presheaves R X) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U P).f 0 = (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.restriction R X U P).app ⦋0⦌ :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

theorem component_augmented (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.Presheaves R X) (x : P.obj (op ⊤))
    (t : Fin 1 → ι) : component R X U P ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U P).f 0 x) t =
      P.map (homOfLE (show ((N).obj (op ⦋0⦌)).obj t ≤ ⊤ from le_top)).op x := by
  rw [augmentation_f_zero]
  exact congrArg (fun f : P.obj (op ⊤) ⟶ P.obj (op (((N).obj (op ⦋0⦌)).obj t)) => f x)
    (Pi.lift_comp_π (fun a : ((N).obj (op ⦋0⦌)).I =>
      P.map (homOfLE (show ((N).obj (op ⦋0⦌)).obj a ≤ ⊤ from le_top)).op) t)

theorem map_assemble {P Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.Presheaves R X} (φ : P ⟶ Q)
    (x : Q.obj (op ⊤)) (y : ∀ i, P.obj (op (U i)))
    (hy : ∀ i, φ.app _ (y i) = Q.map (U i).leTop.op x) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).map φ).f 0 (assemble R X U P y) =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U Q).f 0 x := by
  apply Concrete.limit_ext (Discrete.functor
    (fun a : ((N).obj (op ⦋0⦌)).I => Q.obj (op (((N).obj (op ⦋0⦌)).obj a))))
  intro t
  change component R X U Q (((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).map φ).f 0
      (assemble R X U P y)) t.as =
    component R X U Q ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U Q).f 0 x) t.as
  have hn := congrArg (fun f => f (y (t.as 0))) (φ.naturality (singleProjection R X U t.as).op)
  have hc : Q.map (U (t.as 0)).leTop.op ≫ Q.map (singleProjection R X U t.as).op =
      Q.map (homOfLE (show ((N).obj (op ⦋0⦌)).obj t.as ≤ ⊤ from le_top)).op :=
    (Q.map_comp _ _).symm.trans (congrArg Q.map (Subsingleton.elim _ _))
  exact (map_component R X U φ (assemble R X U P y) t.as).trans
    ((congrArg (φ.app _) (component_assemble R X U P y t.as)).trans
      (hn.trans ((congrArg (Q.map (singleProjection R X U t.as).op) (hy (t.as 0))).trans
        ((congrArg (fun f => f x) hc).trans (component_augmented R X U Q x t.as).symm))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechLift
