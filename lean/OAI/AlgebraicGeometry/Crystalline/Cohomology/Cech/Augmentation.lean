import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SheafExactness
import Mathlib.Algebra.Homology.QuasiIso

/-! # Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Augmentation.CechAugmentation

noncomputable section

/-!
# The canonical augmentation in Čech descent

Identify the natural restriction augmentation with the split local
calculation, so that its degree-zero homology map can be used globally.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

theorem singleton_lift_comp {A : Type*} [Category A] [HasProducts.{u} A]
    {P Q : A} {ι : Type u} (B : ι → A) (a : P ⟶ Q) (b : ∀ i, Q ⟶ B i) :
    (a ≫ Pi.lift (fun _ : PUnit.{u + 1} => 𝟙 Q)) ≫
      Pi.lift (fun i => Pi.π (fun _ : PUnit.{u + 1} => Q) PUnit.unit ≫ b i) =
        Pi.lift (fun i => a ≫ b i) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Category.id_comp]

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (P : Presheaf.CechPresheaf.Presheaves R X)
  (i₀ : ι) (hU : U i₀ = ⊤)

theorem augmentation_f_zero :
    (Presheaf.CechPresheaf.augmentation R X U P).f 0 = (Presheaf.CechPresheaf.restriction R X U P).app ⦋0⦌ := by
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (C := Presheaf.CechPresheaf.complex R X U P) (X := P)
    ((Presheaf.CechPresheaf.restriction R X U P).app ⦋0⦌)
    (Presheaf.CechPresheaf.restriction_cocycle R X U P)

theorem homotopyHom_eq_augmentation :
    (PresheafContraction.CechPresheafContraction.homotopyEquiv R X U P i₀ hU).hom = Presheaf.CechPresheaf.augmentation R X U P := by
  apply HomologicalComplex.from_single_hom_ext
  dsimp only [PresheafContraction.CechPresheafContraction.homotopyEquiv, HomotopyEquiv.symm, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, HomotopyOppositeUnop.HomotopyOpposite.unop, HomologicalComplex.unopFunctor,
    HomologicalComplex.comp_f]
  dsimp only [PresheafContraction.CechPresheafContraction.oppositeHomotopyEquiv,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    HomotopyOppositeUnop.HomotopyOpposite.cofaceIso, HomotopyOppositeUnop.HomotopyOpposite.singleIso,
    HomologicalComplex.Hom.isoOfComponents]
  change ((CochainComplex.single₀ (Presheaf.CechPresheaf.Presheaves R X)).map
    (PresheafContraction.CechPresheafContraction.pointIso R X P).inv).f 0 ≫
    (𝟙 _ ≫ ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering _ _).obj
        (((FormalCoproduct.evalOp X.Opens (Presheaf.CechPresheaf.Presheaves R X)).obj
          (Presheaf.CechPresheaf.intersectionCoefficients R X P)).rightOp)).obj
            (Contraction.CechContraction.augmented X U))).f 0).unop ≫ 𝟙 _) = _
  rw [CochainComplex.single₀_map_f_zero,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  simp only [Category.id_comp]
  change (PresheafContraction.CechPresheafContraction.pointIso R X P).inv ≫
    ((FormalCoproduct.evalOp X.Opens (Presheaf.CechPresheaf.Presheaves R X)).obj
      (Presheaf.CechPresheaf.intersectionCoefficients R X P)).map
        ((Contraction.CechContraction.augmented X U).hom.app (op ⦋0⦌)).op ≫ 𝟙 _ = _
  refine (congrArg (fun t => (PresheafContraction.CechPresheafContraction.pointIso R X P).inv ≫ t)
    (Category.comp_id (((FormalCoproduct.evalOp X.Opens (Presheaf.CechPresheaf.Presheaves R X)).obj
      (Presheaf.CechPresheaf.intersectionCoefficients R X P)).map
        ((Contraction.CechContraction.augmented X U).hom.app (op ⦋0⦌)).op))).trans ?_
  refine Eq.trans ?_ (augmentation_f_zero R X U P).symm
  dsimp only [PresheafContraction.CechPresheafContraction.pointIso, Iso.trans_inv]
  let A := (FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)
  change ((PresheafContraction.CechPresheafContraction.intersectionTopIso R X P).inv ≫
    Pi.lift (fun _ : PUnit => 𝟙 (Presheaf.CechPresheaf.intersection R X P ⊤))) ≫
      Pi.lift (fun i : A.I => Pi.π (fun _ : PUnit => Presheaf.CechPresheaf.intersection R X P ⊤) PUnit.unit ≫
        (Presheaf.CechPresheaf.intersectionCoefficients R X P).map (homOfLE le_top : A.obj i ⟶ ⊤).op) =
    Pi.lift (fun i : A.I => Presheaf.CechPresheaf.restrictToIntersection R X P (A.obj i))
  refine (singleton_lift_comp (fun i : A.I => Presheaf.CechPresheaf.intersection R X P (A.obj i))
    (PresheafContraction.CechPresheafContraction.intersectionTopIso R X P).inv
      (fun i => (Presheaf.CechPresheaf.intersectionCoefficients R X P).map
        (homOfLE le_top : A.obj i ⟶ ⊤).op)).trans ?_
  congr 1
  funext i
  apply NatTrans.ext
  funext V
  change P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp]
  congr 1

include hU in
/-- The canonical augmentation is a quasi-isomorphism for a split covering family. -/
theorem split_quasiIso : QuasiIso (Presheaf.CechPresheaf.augmentation R X U P) := by
  rw [← homotopyHom_eq_augmentation R X U P i₀ hU]
  infer_instance

include hU in
/-- The canonical augmentation remains a quasi-isomorphism after sheafification. -/
theorem split_sheafQuasiIso : QuasiIso (Presheaf.CechPresheaf.sheafAugmentation R X U P) := by
  change QuasiIso (((Presheaf.CechPresheaf.sheafification R X).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (Presheaf.CechPresheaf.augmentation R X U P))
  rw [← homotopyHom_eq_augmentation R X U P i₀ hU]
  exact HomotopyEquiv.quasiIso_hom (PresheafContraction.CechPresheafContraction.sheafHomotopyEquiv R X U P i₀ hU)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Augmentation.CechAugmentation
