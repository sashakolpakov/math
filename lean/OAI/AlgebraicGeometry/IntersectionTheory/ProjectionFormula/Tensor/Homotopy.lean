import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.CategoryTheory.Shift.Quotient

/-! # Homotopy -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Homotopy

noncomputable section

/-! Tensoring with an actual cochain complex defines a functor on the
homotopy category and commutes with shifts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)

local instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (ModuleCat.{0} R)) (.up ℤ) := by
  intro n
  infer_instance

def complexFunctor : CochainComplex (ModuleCat.{0} R) ℤ ⥤
    CochainComplex (ModuleCat.{0} R) ℤ :=
  (curriedTensor (ModuleCat.{0} R)).map₂CochainComplex.flip.obj K

instance complex_additive : (complexFunctor R K).Additive where
  map_add {P Q} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (HomologicalComplex.mapBifunctorMap (f + g) (𝟙 K) (curriedTensor (ModuleCat.{0} R)) (.up ℤ)).f n =
      (HomologicalComplex.mapBifunctorMap f (𝟙 K) (curriedTensor (ModuleCat.{0} R)) (.up ℤ)).f n +
      (HomologicalComplex.mapBifunctorMap g (𝟙 K) (curriedTensor (ModuleCat.{0} R)) (.up ℤ)).f n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    simp only [HomologicalComplex.add_f_apply, Preadditive.comp_add, HomologicalComplex.ι_mapBifunctorMap,
      Functor.map_add, NatTrans.app_add, Preadditive.add_comp]

theorem respects_homotopy {P Q : CochainComplex (ModuleCat.{0} R) ℤ}
    (f g : P ⟶ Q) (h : Homotopy f g) :
    (HomotopyCategory.quotient _ _).map ((complexFunctor R K).map f) =
      (HomotopyCategory.quotient _ _).map ((complexFunctor R K).map g) :=
  HomotopyCategory.eq_of_homotopy _ _
    (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 K) (curriedTensor (ModuleCat.{0} R)) (.up ℤ))

def homotopyFunctor : HomotopyCategory (ModuleCat.{0} R) (.up ℤ) ⥤
    HomotopyCategory (ModuleCat.{0} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift _
    (complexFunctor R K ⋙ HomotopyCategory.quotient _ _) (by
      intro P Q f g h
      exact respects_homotopy R K f g h.some)

instance homotopy_additive : (homotopyFunctor R K).Additive := by
  have : (HomotopyCategory.quotient _ _ ⋙ homotopyFunctor R K).Additive :=
    Functor.additive_of_iso (CategoryTheory.Quotient.lift.isLift _
      (complexFunctor R K ⋙ HomotopyCategory.quotient _ _) _).symm
  exact Functor.additive_of_full_essSurj_comp (HomotopyCategory.quotient _ _) _

instance complex_commShift : (complexFunctor R K).CommShift ℤ := by
  unfold complexFunctor
  infer_instance

instance homotopy_commShift : (homotopyFunctor R K).CommShift ℤ := by
  unfold homotopyFunctor
  exact CategoryTheory.Quotient.liftCommShift
    (complexFunctor R K ⋙ HomotopyCategory.quotient _ _)
    (homotopic (ModuleCat.{0} R) (.up ℤ)) ℤ _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Homotopy
