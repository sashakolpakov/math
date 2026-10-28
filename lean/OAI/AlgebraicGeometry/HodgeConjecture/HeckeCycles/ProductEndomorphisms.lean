import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Product Endomorphisms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms.CM

noncomputable section

/-! The two axis endomorphisms of a commutative group product and their
sum commute with group isomorphisms and actual scheme base change. These
are the extending endomorphisms used to detect the H1 group-law formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme}

local instance one_group (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] :
    IsMonHom (1 : X ⟶ Y) := (1 : Grp.mk X ⟶ Grp.mk Y).hom.isMonHom_hom

local instance mul_group {X Y : Over S} [GrpObj X] [GrpObj Y] [IsCommMonObj Y]
    (f g : X ⟶ Y) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) :=
  (Grp.ofHom f * Grp.ofHom g).hom.isMonHom_hom

variable (A : Over S) [GrpObj A] [IsCommMonObj A]

def axis : A ⟶ A ⊗ A := lift (𝟙 A) (1 : A ⟶ A)
def left : A ⊗ A ⟶ A ⊗ A := lift (fst A A) (1 : A ⊗ A ⟶ A)
def right : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (1 : A ⊗ A ⟶ A)
def fold : A ⊗ A ⟶ A ⊗ A := left A * right A

instance : IsMonHom (axis A) := inferInstanceAs (IsMonHom (lift (𝟙 A) (1 : A ⟶ A)))
instance : IsMonHom (left A) := inferInstanceAs (IsMonHom (lift (fst A A) (1 : A ⊗ A ⟶ A)))
instance : IsMonHom (right A) := inferInstanceAs (IsMonHom (lift (snd A A) (1 : A ⊗ A ⟶ A)))
instance : IsMonHom (fold A) := inferInstanceAs (IsMonHom (left A * right A))

@[reassoc] theorem left_fst : left A ≫ fst A A = fst A A := lift_fst _ _
@[reassoc] theorem left_snd : left A ≫ snd A A = 1 := lift_snd _ _
@[reassoc] theorem right_fst : right A ≫ fst A A = snd A A := lift_fst _ _
@[reassoc] theorem right_snd : right A ≫ snd A A = 1 := lift_snd _ _

theorem fold_fst : fold A ≫ fst A A = μ[A] := by
  rw [fold, MonObj.mul_comp, left_fst, right_fst]
  change lift (fst A A) (snd A A) ≫ μ[A] = _
  rw [lift_fst_snd, Category.id_comp]

variable {B : Over S} [GrpObj B] [IsCommMonObj B] (e : A ≅ B) [IsMonHom e.hom]

@[reassoc] theorem left_iso : left A ≫ (e.hom ⊗ₘ e.hom) = (e.hom ⊗ₘ e.hom) ≫ left B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, left_fst, left_fst_assoc]
  · simp only [Category.assoc, tensorHom_snd, left_snd, left_snd_assoc,
      MonObj.one_comp, MonObj.comp_one]

@[reassoc] theorem right_iso : right A ≫ (e.hom ⊗ₘ e.hom) = (e.hom ⊗ₘ e.hom) ≫ right B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, right_fst, right_fst_assoc, tensorHom_snd]
  · simp only [Category.assoc, tensorHom_snd, right_snd, right_snd_assoc,
      MonObj.one_comp, MonObj.comp_one]

theorem fold_iso : fold A ≫ (e.hom ⊗ₘ e.hom) = (e.hom ⊗ₘ e.hom) ≫ fold B := by
  rw [fold, fold, MonObj.mul_comp, left_iso, right_iso, MonObj.comp_mul]

variable {T : Scheme} (b : T ⟶ S)

local notation "PB" => Over.pullback b
local instance : GrpObj ((PB).obj A) := Functor.grpObjObj (F := Over.pullback b)
local instance : IsCommMonObj ((PB).obj A) := Functor.isCommMonObj_obj (F := Over.pullback b)
local instance : GrpObj ((PB).obj (A ⊗ A)) := Functor.grpObjObj (F := Over.pullback b)
local instance : IsCommMonObj ((PB).obj (A ⊗ A)) :=
  Functor.isCommMonObj_obj (F := Over.pullback b)

def productBaseChange : (PB).obj (A ⊗ A) ≅ (PB).obj A ⊗ (PB).obj A :=
  (Functor.Monoidal.μIso PB A A).symm

@[reassoc] theorem left_baseChange :
    (PB).map (left A) ≫ (productBaseChange A b).hom =
      (productBaseChange A b).hom ≫ left ((PB).obj A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [productBaseChange, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      Category.assoc, Functor.OplaxMonoidal.δ_fst, left_fst, ← Functor.map_comp]
  · simp only [productBaseChange, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      Category.assoc, Functor.OplaxMonoidal.δ_snd, left_snd, ← Functor.map_comp,
      Functor.map_one, MonObj.comp_one]

@[reassoc] theorem right_baseChange :
    (PB).map (right A) ≫ (productBaseChange A b).hom =
      (productBaseChange A b).hom ≫ right ((PB).obj A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [productBaseChange, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      Category.assoc, Functor.OplaxMonoidal.δ_fst, right_fst,
      Functor.OplaxMonoidal.δ_snd, ← Functor.map_comp]
  · simp only [productBaseChange, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      Category.assoc, Functor.OplaxMonoidal.δ_snd, right_snd, ← Functor.map_comp,
      Functor.map_one, MonObj.comp_one]

omit [IsCommMonObj A] in
theorem productBaseChange_group : IsMonHom (productBaseChange A b).hom := by
  let : IsMonHom (Functor.Monoidal.μIso PB A A).hom :=
    inferInstanceAs (IsMonHom (Functor.LaxMonoidal.μ PB A A))
  exact inferInstanceAs (IsMonHom (Functor.Monoidal.μIso PB A A).inv)

theorem fold_baseChange :
    (PB).map (fold A) ≫ (productBaseChange A b).hom =
      (productBaseChange A b).hom ≫ fold ((PB).obj A) := by
  let : IsMonHom (productBaseChange A b).hom := productBaseChange_group A b
  rw [fold, fold, Functor.map_mul, MonObj.mul_comp, left_baseChange, right_baseChange,
    MonObj.comp_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms.CM
