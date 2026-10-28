import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.MappingCone
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.CochainShift
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Triangulated -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Triangulated

noncomputable section

/-! The total tensor functor preserves the native cone triangles and hence
defines a triangulated functor on the homotopy category. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Pretriangulated _root_.CochainComplex _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
variable {P Q : CochainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

theorem hom_inr :
    (Homotopy.complexFunctor R K).map (mappingCone.inr f) ≫
      (MappingCone.iso R K f).hom =
    mappingCone.inr ((Homotopy.complexFunctor R K).map f) := by
  have h : mappingCone.inr ((Homotopy.complexFunctor R K).map f) ≫
      MappingCone.inv R K f =
      (Homotopy.complexFunctor R K).map (mappingCone.inr f) :=
    mappingCone.inr_desc _ _ _ _
  rw [← h, Category.assoc]
  change _ ≫ (MappingCone.iso R K f).inv ≫ (MappingCone.iso R K f).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

theorem hom_δ :
    (MappingCone.iso R K f).hom ≫
      (mappingCone.triangle ((Homotopy.complexFunctor R K).map f)).mor₃ =
    (Homotopy.complexFunctor R K).map (mappingCone.triangle f).mor₃ ≫
      ((Homotopy.complexFunctor R K).commShiftIso (1 : ℤ)).hom.app P := by
  change _ = (Homotopy.complexFunctor R K).map
    (Cocycle.homOf ((-mappingCone.fst f).rightShift 1 0 (zero_add 1))) ≫ _
  rw [CochainShift.homOf_rightShift]
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, mappingCone.triangle, Triangle.mk_mor₃,
    Cocycle.homOf_f, Cocycle.rightShift_coe, Tensor.Cochain.mapCocycle_coe,
    Cocycle.coe_neg, Tensor.Cochain.map_neg,
    Cochain.rightShift_v _ 1 0 (zero_add 1) n n (add_zero n) (n + 1) rfl,
    Cochain.neg_v, Preadditive.comp_neg, Preadditive.neg_comp]
  change -((MappingCone.hom R K f).f n ≫ _) = _
  simp only [MappingCone.hom, mappingCone.lift_f_fst_v_assoc,
    Tensor.Cochain.mapCocycle_coe]

def triangleIso :
    (Homotopy.complexFunctor R K).mapTriangle.obj (mappingCone.triangle f) ≅
    mappingCone.triangle ((Homotopy.complexFunctor R K).map f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (MappingCone.iso R K f)
    (by simp [CategoryTheory.Functor.mapTriangle])
    (by simpa [CategoryTheory.Functor.mapTriangle] using hom_inr R K f)
    (by
      change (_ ≫ _) ≫ (CategoryTheory.shiftFunctor _ (1 : ℤ)).map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact (hom_δ R K f).symm)

def liftIso : HomotopyCategory.quotient _ _ ⋙ Homotopy.homotopyFunctor R K ≅
    Homotopy.complexFunctor R K ⋙ HomotopyCategory.quotient _ _ :=
  CategoryTheory.Quotient.lift.isLift _ _ _

instance liftIso_commShift : NatTrans.CommShift (liftIso R K).hom ℤ := by
  unfold liftIso Homotopy.homotopyFunctor
  exact CategoryTheory.Quotient.liftCommShift_compatibility _ _ ℤ _

def trianglehIso :
    (Homotopy.homotopyFunctor R K).mapTriangle.obj (mappingCone.triangleh f) ≅
    mappingCone.triangleh ((Homotopy.complexFunctor R K).map f) :=
  (CategoryTheory.Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (CategoryTheory.Functor.mapTriangleIso (liftIso R K)).app _ ≪≫
    (CategoryTheory.Functor.mapTriangleCompIso _ _).app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso (triangleIso R K f)

instance homotopy_triangulated : (Homotopy.homotopyFunctor R K).IsTriangulated where
  map_distinguished := by
    rintro T ⟨P, Q, f, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(Homotopy.homotopyFunctor R K).mapTriangle.mapIso e ≪≫
      trianglehIso R K f⟩⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Triangulated
