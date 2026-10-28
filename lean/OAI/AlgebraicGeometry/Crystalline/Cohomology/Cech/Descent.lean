import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Algebra.Homology.TotalComplex

/-! # Descent -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent

noncomputable section

/-!
# Cohomology: Čech de Rham complexes and their restriction maps

The Čech terms use the actual intersections in the scheme's lattice of opens.
The construction works for any family of opens; comparison with sheaf
hypercohomology additionally requires the covering and acyclicity arguments.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
variable {ι : Type u} (U : ι → X.left.Opens)

abbrev Presheaves := X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R

def cechFunctor : Presheaves R X ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  cechComplexFunctor U

instance cech_preservesZero : (cechFunctor R X U).PreservesZeroMorphisms where
  map_zero P Q := by
    ext n : 1
    let E := (FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)
    change (Limits.Pi.map (fun i : E.I => (0 : P.obj (op (E.obj i)) ⟶ Q.obj (op (E.obj i))))) = 0
    apply Pi.hom_ext
    intro v
    simp only [Pi.map_π, comp_zero, zero_comp]

/-- The double complex of algebraic forms on all finite intersections. -/
def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((cechFunctor R X U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

/-- Extend both degrees by zero before forming the signed total complex. -/
def bicomplexInt :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (bicomplex R X U)).extend ComplexShape.embeddingUpNat

/-- The total Čech de Rham complex with the standard signs. -/
def totalComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (bicomplexInt R X U).total (ComplexShape.up ℤ)

/-- Global algebraic forms before deriving global sections. -/
def globalSectionsComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  (((evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

/-- The cosimplicial diagram underlying the Čech complex. -/
def cosimplicialFunctor : Presheaves R X ⥤ CosimplicialObject (ModuleCat.{u} R) :=
  FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech

/-- Restrict a global section to each intersection in the Čech nerve. -/
def restriction (P : Presheaves R X) :
    (Functor.const SimplexCategory).obj (P.obj (op ⊤)) ⟶
      (cosimplicialFunctor R X U).obj P where
  app n := Pi.lift (fun _ => P.map (homOfLE le_top).op)
  naturality n m f := by
    let En := (FormalCoproduct.mk ι U).cech.obj (op n)
    let Em := (FormalCoproduct.mk ι U).cech.obj (op m)
    let φ : Em ⟶ En := (FormalCoproduct.mk ι U).cech.map f.op
    change (𝟙 (P.obj (op ⊤))) ≫ (Pi.lift (fun _ => P.map (homOfLE le_top).op)) =
      (Pi.lift (fun _ => P.map (homOfLE le_top).op)) ≫
        (Pi.lift (fun i : Em.I => Pi.π (fun j : En.I => P.obj (op (En.obj j))) (φ.f i) ≫
          P.map (φ.φ i).op))
    apply Pi.hom_ext
    intro v
    simp only [Category.id_comp, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    rw [← P.map_comp]
    congr 1

/-- The restriction to degree zero is a Čech cocycle. -/
theorem restriction_cocycle (P : Presheaves R X) :
    (restriction R X U P).app ⦋0⦌ ≫ ((cechFunctor R X U).obj P).d 0 1 = 0 := by
  let Y : SimplexCategory ⥤ ModuleCat.{u} R := (cosimplicialFunctor R X U).obj P
  let a : (Functor.const SimplexCategory).obj (P.obj (op ⊤)) ⟶ Y := restriction R X U P
  change a.app ⦋0⦌ ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Y.map (SimplexCategory.δ i)) = 0
  simp only [Fin.sum_univ_two,
    Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  have h0 := a.naturality (SimplexCategory.δ (0 : Fin 2))
  have h1 := a.naturality (SimplexCategory.δ (1 : Fin 2))
  change a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (0 : Fin 2)) at h0
  change a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (1 : Fin 2)) at h1
  rw [← h0, ← h1, add_neg_cancel]

/-- The canonical map from global sections into the Čech complex. -/
def augmentation (P : Presheaves R X) :
    (CochainComplex.single₀ (ModuleCat.{u} R)).obj (P.obj (op ⊤)) ⟶
      (cechFunctor R X U).obj P :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(restriction R X U P).app ⦋0⦌, restriction_cocycle R X U P⟩

theorem augmentation_natural {P Q : Presheaves R X} (f : P ⟶ Q) :
    (CochainComplex.single₀ (ModuleCat.{u} R)).map (f.app (op ⊤)) ≫ augmentation R X U Q =
      augmentation R X U P ≫ (cechFunctor R X U).map f := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, augmentation,
    CochainComplex.single₀_map_f_zero]
  let E := (FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)
  change f.app (op ⊤) ≫ (Pi.lift fun i : E.I => Q.map (homOfLE le_top).op) =
    (Pi.lift fun i : E.I => P.map (homOfLE le_top).op) ≫
      Limits.Pi.map (fun i : E.I => f.app (op (E.obj i)))
  apply Pi.hom_ext
  intro v
  simp only [Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
  exact (f.naturality (homOfLE le_top).op).symm

/-- The Čech augmentation is natural in the coefficient presheaf. -/
def augmentationNat :
    (evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤) ⋙
      CochainComplex.single₀ (ModuleCat.{u} R) ⟶ cechFunctor R X U where
  app P := augmentation R X U P
  naturality _ _ f := augmentation_natural R X U f

/-- Global forms as a double complex concentrated in Čech degree zero. -/
def globalSectionsBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (((evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤) ⋙
    CochainComplex.single₀ (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

/-- The augmentation commutes both with Čech coboundaries and with the
de Rham differential. -/
def augmentationBicomplex : globalSectionsBicomplex R X ⟶ bicomplex R X U :=
  ((augmentationNat R X U).mapHomologicalComplex (ComplexShape.up ℕ)).app
    (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent
