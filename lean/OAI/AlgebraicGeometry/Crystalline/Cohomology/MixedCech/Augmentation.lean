import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.SheafExactness
import Mathlib.Algebra.Homology.QuasiIso

/-! # Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Augmentation.MixedCechAugmentation

noncomputable section

/-!
Mixed-universe version for the native crystalline coefficient modules.

# The canonical augmentation in Čech descent

Identify the natural restriction augmentation with the split local
calculation, so that its degree-zero homology map can be used globally.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u v

theorem singleton_lift_comp {A : Type*} [Category A] [HasProducts.{u} A]
    {P Q : A} {ι : Type u} (B : ι → A) (a : P ⟶ Q) (b : ∀ i, Q ⟶ B i) :
    (a ≫ Pi.lift (fun _ : PUnit.{u + 1} => 𝟙 Q)) ≫
      Pi.lift (fun i => Pi.π (fun _ : PUnit.{u + 1} => Q) PUnit.unit ≫ b i) =
        Pi.lift (fun i => a ≫ b i) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Category.id_comp]

variable (R : Type v) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (P : Presheaf.MixedCechPresheaf.Presheaves R X)
  (i₀ : ι) (hU : U i₀ = ⊤)

theorem augmentation_f_zero :
    (Presheaf.MixedCechPresheaf.augmentation R X U P).f 0 = (Presheaf.MixedCechPresheaf.restriction R X U P).app ⦋0⦌ := by
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (C := Presheaf.MixedCechPresheaf.complex R X U P) (X := P)
    ((Presheaf.MixedCechPresheaf.restriction R X U P).app ⦋0⦌)
    (Presheaf.MixedCechPresheaf.restriction_cocycle R X U P)

theorem homotopyHom_eq_augmentation :
    (PresheafContraction.MixedCechPresheafContraction.homotopyEquiv R X U P i₀ hU).hom = Presheaf.MixedCechPresheaf.augmentation R X U P := by
  apply HomologicalComplex.from_single_hom_ext
  dsimp only [PresheafContraction.MixedCechPresheafContraction.homotopyEquiv, HomotopyEquiv.symm, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, HomotopyOppositeUnop.HomotopyOpposite.unop, HomologicalComplex.unopFunctor,
    HomologicalComplex.comp_f]
  dsimp only [PresheafContraction.MixedCechPresheafContraction.oppositeHomotopyEquiv,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    HomotopyOppositeUnop.HomotopyOpposite.cofaceIso, HomotopyOppositeUnop.HomotopyOpposite.singleIso,
    HomologicalComplex.Hom.isoOfComponents]
  change ((CochainComplex.single₀ (Presheaf.MixedCechPresheaf.Presheaves R X)).map
    (PresheafContraction.MixedCechPresheafContraction.pointIso R X P).inv).f 0 ≫
    (𝟙 _ ≫ ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering _ _).obj
        (((FormalCoproduct.evalOp X.Opens (Presheaf.MixedCechPresheaf.Presheaves R X)).obj
          (Presheaf.MixedCechPresheaf.intersectionCoefficients R X P)).rightOp)).obj
            (Cech.Contraction.CechContraction.augmented X U))).f 0).unop ≫ 𝟙 _) = _
  rw [CochainComplex.single₀_map_f_zero,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  simp only [Category.id_comp]
  change (PresheafContraction.MixedCechPresheafContraction.pointIso R X P).inv ≫
    ((FormalCoproduct.evalOp X.Opens (Presheaf.MixedCechPresheaf.Presheaves R X)).obj
      (Presheaf.MixedCechPresheaf.intersectionCoefficients R X P)).map
        ((Cech.Contraction.CechContraction.augmented X U).hom.app (op ⦋0⦌)).op ≫ 𝟙 _ = _
  refine (congrArg (fun t => (PresheafContraction.MixedCechPresheafContraction.pointIso R X P).inv ≫ t)
    (Category.comp_id (((FormalCoproduct.evalOp X.Opens (Presheaf.MixedCechPresheaf.Presheaves R X)).obj
      (Presheaf.MixedCechPresheaf.intersectionCoefficients R X P)).map
        ((Cech.Contraction.CechContraction.augmented X U).hom.app (op ⦋0⦌)).op))).trans ?_
  refine Eq.trans ?_ (augmentation_f_zero R X U P).symm
  dsimp only [PresheafContraction.MixedCechPresheafContraction.pointIso, Iso.trans_inv]
  let A := (FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)
  change ((PresheafContraction.MixedCechPresheafContraction.intersectionTopIso R X P).inv ≫
    Pi.lift (fun _ : PUnit => 𝟙 (Presheaf.MixedCechPresheaf.intersection R X P ⊤))) ≫
      Pi.lift (fun i : A.I => Pi.π (fun _ : PUnit => Presheaf.MixedCechPresheaf.intersection R X P ⊤) PUnit.unit ≫
        (Presheaf.MixedCechPresheaf.intersectionCoefficients R X P).map (homOfLE le_top : A.obj i ⟶ ⊤).op) =
    Pi.lift (fun i : A.I => Presheaf.MixedCechPresheaf.restrictToIntersection R X P (A.obj i))
  refine (singleton_lift_comp (fun i : A.I => Presheaf.MixedCechPresheaf.intersection R X P (A.obj i))
    (PresheafContraction.MixedCechPresheafContraction.intersectionTopIso R X P).inv
      (fun i => (Presheaf.MixedCechPresheaf.intersectionCoefficients R X P).map
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
theorem split_quasiIso : QuasiIso (Presheaf.MixedCechPresheaf.augmentation R X U P) := by
  rw [← homotopyHom_eq_augmentation R X U P i₀ hU]
  infer_instance

include hU in
/-- The canonical augmentation remains a quasi-isomorphism after sheafification. -/
theorem split_sheafQuasiIso : QuasiIso (Presheaf.MixedCechPresheaf.sheafAugmentation R X U P) := by
  change QuasiIso (((Presheaf.MixedCechPresheaf.sheafification R X).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (Presheaf.MixedCechPresheaf.augmentation R X U P))
  rw [← homotopyHom_eq_augmentation R X U P i₀ hU]
  exact HomotopyEquiv.quasiIso_hom (PresheafContraction.MixedCechPresheafContraction.sheafHomotopyEquiv R X U P i₀ hU)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Augmentation.MixedCechAugmentation
