import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Global Sections Iso -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso

noncomputable section

/-!
# Global sections of the Čech presheaf complex

Evaluation at the whole scheme gives the direct Čech complex used by
the de Rham construction. The comparison preserves the canonical
augmentation from global sections.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

theorem lift_comparison {A B : Type*} [Category A] [Category B]
    [HasProducts.{u} A] [HasProducts.{u} B] (G : A ⥤ B) {α : Type u}
    (F : α → A) (T : α → B) (Y : A) (a : ∀ i, Y ⟶ F i)
    (g : ∀ i, G.obj (F i) ⟶ T i) :
    G.map (Pi.lift a) ≫ (piComparison G F ≫ Limits.Pi.map g) =
      Pi.lift (fun i => G.map (a i) ≫ g i) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π, piComparison_comp_π_assoc]
  rw [← Category.assoc, ← G.map_comp, Pi.lift_comp_π]

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens) (P : Presheaf.CechPresheaf.Presheaves R X.left)

def coefficientIso :
    Presheaf.CechPresheaf.intersectionCoefficients R X.left P ⋙
      (evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤) ≅ P :=
  NatIso.ofComponents (fun V => P.mapIso (eqToIso (congrArg op (top_inf_eq (a := V.unop))))) (by
    intro V W f
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1)

def complexIso :
    SectionsExactness.CechSectionsExactness.sections R X.left U P ⊤ ≅ (Descent.CechDescent.cechFunctor R X U).obj P :=
  CoefficientChange.CechCoefficientChange.complexIso ((evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤))
    (FormalCoproduct.mk ι U).cech (Presheaf.CechPresheaf.intersectionCoefficients R X.left P) ≪≫
      (cechComplexFunctor U).mapIso (coefficientIso R X P)

def sourceIso :=
  (HomologicalComplex.singleMapHomologicalComplex
    ((evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)) (ComplexShape.up ℕ) 0).app P

theorem augmentation_comp :
    (sourceIso R X P).inv ≫ AugmentedSections.CechAugmentedSections.augmentation R X.left U P ⊤ ≫ (complexIso R X U P).hom =
      Descent.CechDescent.augmentation R X U P := by
  apply HomologicalComplex.from_single_hom_ext
  change (𝟙 _ ≫ (((Presheaf.CechPresheaf.augmentation R X.left U P).f 0).app (op ⊤) ≫
    (complexIso R X U P).hom.f 0)) = (Descent.CechDescent.restriction R X U P).app ⦋0⦌
  rw [Category.id_comp]
  have ha := congrArg (fun t : P ⟶ (Presheaf.CechPresheaf.complex R X.left U P).X 0 => t.app (op ⊤))
    (Augmentation.CechAugmentation.augmentation_f_zero R X.left U P)
  rw [ha]
  let E := (evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)
  let A := (FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)
  let F := fun v : A.I => Presheaf.CechPresheaf.intersection R X.left P (A.obj v)
  change ((Presheaf.CechPresheaf.restriction R X.left U P).app ⦋0⦌).app (op ⊤) ≫
    (piComparison E F ≫ Limits.Pi.map (fun v : A.I => (coefficientIso R X P).hom.app (op (A.obj v)))) =
      Pi.lift (fun v : A.I => P.map (homOfLE le_top : A.obj v ⟶ ⊤).op)
  refine (lift_comparison E F (fun v => P.obj (op (A.obj v))) P
    (fun v => Presheaf.CechPresheaf.restrictToIntersection R X.left P (A.obj v))
    (fun v => (coefficientIso R X P).hom.app (op (A.obj v)))).trans ?_
  congr 1
  funext v
  change P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso
