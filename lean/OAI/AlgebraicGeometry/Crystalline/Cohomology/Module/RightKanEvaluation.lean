import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Right Kan Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.RightKanEvaluation.ModuleRightKanEvaluation

noncomputable section

/-! # Natural pointwise evaluation of module-valued right Kan extension -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ w

abbrev Modules (R : Type w) [Ring R] := ModuleCat.{w} R

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (R : Type (max u₁ v₁ u₂ v₂)) [Ring R] (F : C ⥤ D) (X : D)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.RightKanEvaluation.ModuleRightKanEvaluation.Modules R

local instance diagramLimits : HasLimitsOfShape (StructuredArrow X F) V := ModuleCat.hasLimitsOfShape

def iso : F.ran ⋙ (evaluation D V).obj X ≅
    (Functor.whiskeringLeft _ _ V).obj (StructuredArrow.proj X F) ⋙ lim :=
  NatIso.ofComponents (fun P => F.ranObjObjIsoLimit P X) (fun {P Q} φ => by
    apply limit.hom_ext
    intro T
    let εP : F ⋙ F.ran.obj P ⟶ P := F.ranCounit.app P
    let εQ : F ⋙ F.ran.obj Q ⟶ Q := F.ranCounit.app Q
    let τ : F.ran.obj P ⟶ F.ran.obj Q := F.ran.map φ
    let eP : (F.ran.obj P).obj X ≅ limit (StructuredArrow.proj X F ⋙ P) := F.ranObjObjIsoLimit P X
    let eQ : (F.ran.obj Q).obj X ≅ limit (StructuredArrow.proj X F ⋙ Q) := F.ranObjObjIsoLimit Q X
    let πP : limit (StructuredArrow.proj X F ⋙ P) ⟶ P.obj T.right := limit.π _ T
    let πQ : limit (StructuredArrow.proj X F ⋙ Q) ⟶ Q.obj T.right := limit.π _ T
    have h : τ.app (F.obj T.right) ≫ εQ.app T.right = εP.app T.right ≫ φ.app T.right :=
      congr_app (F.ranCounit.naturality φ) T.right
    have hP : eP.hom ≫ πP = (F.ran.obj P).map T.hom ≫ εP.app T.right :=
      F.ranObjObjIsoLimit_hom_π P X T
    have hQ : eQ.hom ≫ πQ = (F.ran.obj Q).map T.hom ≫ εQ.app T.right :=
      F.ranObjObjIsoLimit_hom_π Q X T
    have hπ : limMap (Functor.whiskerLeft (StructuredArrow.proj X F) φ) ≫ πQ =
        πP ≫ φ.app T.right := limMap_π _ T
    change (τ.app X ≫ eQ.hom) ≫ πQ =
      (eP.hom ≫
        limMap (Functor.whiskerLeft (StructuredArrow.proj X F) φ)) ≫ πQ
    calc
      (τ.app X ≫ eQ.hom) ≫ πQ =
          τ.app X ≫ ((F.ran.obj Q).map T.hom ≫ εQ.app T.right) := by rw [Category.assoc, hQ]
      _ = (F.ran.obj P).map T.hom ≫ (τ.app (F.obj T.right) ≫ εQ.app T.right) := by
        rw [← Category.assoc, ← τ.naturality T.hom, Category.assoc]
      _ = (F.ran.obj P).map T.hom ≫ (εP.app T.right ≫ φ.app T.right) := by rw [h]
      _ = (eP.hom ≫ πP) ≫ φ.app T.right := by rw [hP, Category.assoc]
      _ = (eP.hom ≫ limMap (Functor.whiskerLeft (StructuredArrow.proj X F) φ)) ≫
          πQ := by simp only [Category.assoc, hπ])

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.RightKanEvaluation.ModuleRightKanEvaluation
