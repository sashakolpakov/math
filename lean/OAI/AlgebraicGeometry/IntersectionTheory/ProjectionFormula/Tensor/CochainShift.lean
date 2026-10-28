import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Cochain
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # Cochain Shift -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.CochainShift

noncomputable section

/-! Compatibility of tensoring cocycles with the canonical shift isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
variable {P Q : CochainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}

local instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (ModuleCat.{0} R)) (.up ℤ) := by
  intro n
  infer_instance

theorem homOf_rightShift (z : Cocycle P Q a) :
    (Homotopy.complexFunctor R K).map (Cocycle.homOf (z.rightShift a 0 (zero_add a))) ≫
      ((Homotopy.complexFunctor R K).commShiftIso a).hom.app Q =
    Cocycle.homOf ((Tensor.Cochain.mapCocycle R K z).rightShift a 0 (zero_add a)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (HomologicalComplex.mapBifunctorMap
    (Cocycle.homOf (z.rightShift a 0 (zero_add a))) (𝟙 K)
    (curriedTensor (ModuleCat.{0} R)) (.up ℤ)).f n ≫
      (CochainComplex.mapBifunctorShift₁Iso Q K (curriedTensor (ModuleCat.{0} R)) a).hom.f n = _
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  rw [((curriedTensor (ModuleCat.{0} R)).obj ((Q⟦a⟧).X i)).map_id, Category.id_comp,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f Q K (curriedTensor (ModuleCat.{0} R)) a
      i j n hij (i + a) (n + a) rfl rfl]
  simp only [Cocycle.homOf_f, Cocycle.rightShift_coe, Tensor.Cochain.mapCocycle_coe,
    Cochain.rightShift_v _ a 0 (zero_add a) i i (add_zero i) (i + a) rfl,
    Cochain.rightShift_v _ a 0 (zero_add a) n n (add_zero n) (n + a) rfl]
  rw [Tensor.Cochain.ι_map_assoc R K z.1 n (n + a) i j rfl hij]
  rw [Functor.map_comp, NatTrans.comp_app]
  simp only [Category.assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Category.comp_id]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.CochainShift
