import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Contraction
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Presheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf.MixedCechPresheaf

noncomputable section

/-!
Mixed-universe version for the native crystalline coefficient modules.

# Čech complexes as presheaf complexes

The coefficient presheaf is evaluated on intersections with a varying
open. Applying the Čech functor in the other variable gives the actual
presheaf of Čech cochains, rather than only its global sections.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u v

theorem pi_lift_comp_lift_projection {V : Type*} [Category V] [HasProducts.{u} V]
    {α β : Type u} {P : V} (A : α → V) (B : β → V)
    (a : ∀ i, P ⟶ A i) (f : β → α) (b : ∀ j, A (f j) ⟶ B j) (j : β) :
    ((Pi.lift a) ≫ (Pi.lift (fun i => Pi.π A (f i) ≫ b i))) ≫ Pi.π B j = a (f j) ≫ b j := by
  simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]

variable (R : Type v) [CommRing R] (X : Scheme.{u})

abbrev Presheaves := X.Opensᵒᵖ ⥤ ModuleCat.{max u v} R

/-- Restrict sections by intersecting with a fixed open. -/
def intersection (P : Presheaves R X) (U : X.Opens) : Presheaves R X where
  obj V := P.obj (op (V.unop ⊓ U))
  map f := P.map (homOfLE (inf_le_inf_right U (leOfHom f.unop))).op
  map_id V := by
    have h : (homOfLE (inf_le_inf_right U (leOfHom (𝟙 V).unop))).op = 𝟙 (op (V.unop ⊓ U)) :=
      Subsingleton.elim _ _
    rw [h, P.map_id]
  map_comp f g := by
    rw [← P.map_comp]
    congr 1

/-- Vary the second intersection argument, retaining the presheaf variable. -/
def intersectionCoefficients (P : Presheaves R X) : X.Opensᵒᵖ ⥤ Presheaves R X where
  obj U := intersection R X P U.unop
  map f :=
    { app V := P.map (homOfLE (inf_le_inf_left V.unop (leOfHom f.unop))).op
      naturality V W g := by
        change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
        rw [← P.map_comp, ← P.map_comp]
        congr 1 }
  map_id U := by
    apply NatTrans.ext
    funext V
    change P.map _ = 𝟙 _
    have h : (homOfLE (inf_le_inf_left V.unop (leOfHom (𝟙 U).unop))).op =
        𝟙 (op (V.unop ⊓ U.unop)) := Subsingleton.elim _ _
    rw [h, P.map_id]
  map_comp f g := by
    apply NatTrans.ext
    funext V
    change P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp]
    congr 1

variable {ι : Type u} (U : ι → X.Opens)

/-- Čech cochains on every open, with restriction maps in that open. -/
def complex (P : Presheaves R X) : CochainComplex (Presheaves R X) ℕ :=
  (cechComplexFunctor (A := Presheaves R X) U).obj (intersectionCoefficients R X P)

/-- The underlying cosimplicial presheaf. -/
def cosimplicial (P : Presheaves R X) : CosimplicialObject (Presheaves R X) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj
    (intersectionCoefficients R X P)

def restrictToIntersection (P : Presheaves R X) (V : X.Opens) : P ⟶ intersection R X P V where
  app W := P.map (homOfLE inf_le_left).op
  naturality W Z f := by
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1

theorem restrictToIntersection_map (P : Presheaves R X) {V W : X.Opens} (f : V ⟶ W) :
    restrictToIntersection R X P V = restrictToIntersection R X P W ≫
      (intersectionCoefficients R X P).map f.op := by
  apply NatTrans.ext
  funext Z
  change P.map _ = P.map _ ≫ P.map _
  rw [← P.map_comp]
  congr 1

/-- Restriction of a section to each Čech intersection, naturally in its open. -/
def restriction (P : Presheaves R X) :
    (Functor.const SimplexCategory).obj P ⟶ cosimplicial R X U P where
  app n := Pi.lift (fun i => restrictToIntersection R X P
    (((FormalCoproduct.mk ι U).cech.obj (op n)).obj i))
  naturality n m f := by
    let En := (FormalCoproduct.mk ι U).cech.obj (op n)
    let Em := (FormalCoproduct.mk ι U).cech.obj (op m)
    let φ : Em ⟶ En := (FormalCoproduct.mk ι U).cech.map f.op
    change 𝟙 P ≫ (Pi.lift (fun i : Em.I => restrictToIntersection R X P (Em.obj i))) =
      (Pi.lift (fun i : En.I => restrictToIntersection R X P (En.obj i))) ≫
        (Pi.lift (fun i : Em.I => Pi.π (fun j : En.I => intersection R X P (En.obj j)) (φ.f i) ≫
          (intersectionCoefficients R X P).map (φ.φ i).op))
    apply Pi.hom_ext
    intro i
    change (𝟙 P ≫ (Pi.lift (fun j : Em.I => restrictToIntersection R X P (Em.obj j)))) ≫
        Pi.π (fun j : Em.I => intersection R X P (Em.obj j)) i =
      ((Pi.lift (fun j : En.I => restrictToIntersection R X P (En.obj j))) ≫
        (Pi.lift (fun j : Em.I => Pi.π (fun l : En.I => intersection R X P (En.obj l)) (φ.f j) ≫
          (intersectionCoefficients R X P).map (φ.φ j).op))) ≫
        Pi.π (fun j : Em.I => intersection R X P (Em.obj j)) i
    simp only [Category.id_comp, Pi.lift_comp_π]
    exact (restrictToIntersection_map R X P (φ.φ i)).trans
      (pi_lift_comp_lift_projection (fun j : En.I => intersection R X P (En.obj j))
        (fun j : Em.I => intersection R X P (Em.obj j))
        (fun j => restrictToIntersection R X P (En.obj j)) φ.f
        (fun j => (intersectionCoefficients R X P).map (φ.φ j).op) i).symm

theorem restriction_cocycle (P : Presheaves R X) :
    (restriction R X U P).app ⦋0⦌ ≫ (complex R X U P).d 0 1 = 0 := by
  let Y := cosimplicial R X U P
  let a := restriction R X U P
  change a.app ⦋0⦌ ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Y.map (SimplexCategory.δ i)) = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one,
    pow_one, neg_smul, one_smul, Preadditive.comp_add, Preadditive.comp_neg]
  have h0 := a.naturality (SimplexCategory.δ (0 : Fin 2))
  have h1 := a.naturality (SimplexCategory.δ (1 : Fin 2))
  change a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (0 : Fin 2)) at h0
  change a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (1 : Fin 2)) at h1
  rw [← h0, ← h1, add_neg_cancel]

/-- The actual presheaf augmentation into Čech cochains. -/
def augmentation (P : Presheaves R X) :
    (CochainComplex.single₀ (Presheaves R X)).obj P ⟶ complex R X U P :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(restriction R X U P).app ⦋0⦌, restriction_cocycle R X U P⟩

instance moduleSheafify : HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{max u v} R) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
    { preserves_filtered_colimits := fun _ _ _ =>
        { preservesColimit := fun {F} =>
            preservesColimit_of_preserves_colimit_cocone
              (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
              (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
                (F ⋙ forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})) } }
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v, max u v, u, u} _
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{max u v} R)) :=
    comp_preservesFilteredColimits (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (forget AddCommGrpCat.{max u v})
  exact HasSheafify.mk' _ _
    (plusPlusAdjunction (Opens.grothendieckTopology X) (ModuleCat.{max u v} R))

def sheafification : Presheaves R X ⥤ Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R) :=
  presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R)

instance sheafification_additive : (sheafification R X).Additive := by
  dsimp [sheafification]
  infer_instance

/-- The Čech complex as actual sheaves of modules. -/
def sheafComplex (P : Presheaves R X) :
    CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R)) ℕ :=
  ((sheafification R X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (complex R X U P)

def sheafAugmentation (P : Presheaves R X) :
    ((sheafification R X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ (Presheaves R X)).obj P) ⟶ sheafComplex R X U P :=
  ((sheafification R X).mapHomologicalComplex (ComplexShape.up ℕ)).map (augmentation R X U P)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf.MixedCechPresheaf
