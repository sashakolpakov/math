import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupUnitLaws

/-! # Unit Parameters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.UnitParameters.Construction

noncomputable section

/-! The universal unit configurations are actual group maps on the
original Poincare product scheme, with exact factorizations for arbitrary
test configurations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

abbrev poincareProductSpace : Over S := D.abelian.scheme ⊗ A.scheme

def horizontalUnitParameter : poincareProductSpace D ⟶ poincareProductSpace D :=
  lift (1 : poincareProductSpace D ⟶ D.abelian.scheme) (snd D.abelian.scheme A.scheme)

def verticalUnitParameter : poincareProductSpace D ⟶ poincareProductSpace D :=
  lift (fst D.abelian.scheme A.scheme) (1 : poincareProductSpace D ⟶ A.scheme)

instance horizontalUnitParameter_isMonHom : IsMonHom (horizontalUnitParameter D) := by
  unfold horizontalUnitParameter
  rw [Hom.one_def]
  infer_instance

instance verticalUnitParameter_isMonHom : IsMonHom (verticalUnitParameter D) := by
  unfold verticalUnitParameter
  rw [Hom.one_def]
  infer_instance

theorem horizontalUnitParameter_first : horizontalUnitParameter D ≫ fst D.abelian.scheme A.scheme = 1 :=
  lift_fst _ _

theorem verticalUnitParameter_second : verticalUnitParameter D ≫ snd D.abelian.scheme A.scheme = 1 :=
  lift_snd _ _

theorem horizontalUnitParameter_relation :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme)
      (horizontalUnitParameter D) (𝟙 _) (𝟙 _) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [horizontalUnitParameter, lift_fst, Category.id_comp, one_mul]
  · simp only [horizontalUnitParameter, lift_snd, Category.id_comp]
  · simp only [horizontalUnitParameter, lift_snd, Category.id_comp]

theorem verticalUnitParameter_relation :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme)
      (verticalUnitParameter D) (𝟙 _) (𝟙 _) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [verticalUnitParameter, lift_snd, Category.id_comp, one_mul]
  · simp only [verticalUnitParameter, lift_fst, Category.id_comp]
  · simp only [verticalUnitParameter, lift_fst, Category.id_comp]

theorem horizontalUnitParameter_factor {T : Over S} (a x : T ⟶ poincareProductSpace D)
    (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a x x) :
    x ≫ horizontalUnitParameter D = a := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [horizontalUnitParameter, Category.assoc, lift_fst, MonObj.comp_one] using ha.symm
  · simpa only [horizontalUnitParameter, Category.assoc, lift_snd] using h.2.1.symm

theorem verticalUnitParameter_factor {T : Over S} (a x : T ⟶ poincareProductSpace D)
    (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a x x) :
    x ≫ verticalUnitParameter D = a := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [verticalUnitParameter, Category.assoc, lift_fst] using h.2.1.symm
  · simpa only [verticalUnitParameter, Category.assoc, lift_snd, MonObj.comp_one] using ha.symm

variable {k : Type u} [Field k] {d : ℕ} {Ab : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} (Db : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData Ab)

local instance poincareProductSpace_smooth : Smooth (poincareProductSpace Db).hom := by dsimp; infer_instance

local instance poincareProductSpace_proper : IsProper (poincareProductSpace Db).hom := by dsimp; infer_instance

local instance poincareProductSpace_connected : GeometricallyConnected (poincareProductSpace Db).hom :=
  GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst Db.abelian.scheme.hom Ab.scheme.hom)
    Db.abelian.scheme.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.UnitParameters.Construction
