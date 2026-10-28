import Mathlib

/-! # Initial Constant Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InitialConstantMaps

noncomputable section

/-!
# IntegralComparison: constant-source maps are unchanged along an initial functor

Initiality gives an explicit extension of cones with their cone point
unchanged. This yields the needed degree-zero comparison for constant
coefficients before sheafification.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' u'' v''

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {E : Type u''} [Category.{v''} E]
variable (F : C ⥤ D) [F.Initial] (A : E) (P : D ⥤ E)

def restrict (φ : (Functor.const D).obj A ⟶ P) : (Functor.const C).obj A ⟶ F ⋙ P :=
  Functor.whiskerLeft F φ

def extend (φ : (Functor.const C).obj A ⟶ F ⋙ P) : (Functor.const D).obj A ⟶ P :=
  (Functor.Initial.extendCone.obj ({ pt := A, π := φ } : Cone (F ⋙ P))).π

lemma extend_restrict (φ : (Functor.const D).obj A ⟶ P) : extend F A P (restrict F A P φ) = φ := by
  apply NatTrans.ext
  funext X
  change φ.app (F.obj (Functor.Initial.lift F X)) ≫ P.map (Functor.Initial.homToLift F X) = φ.app X
  simpa using (φ.naturality (Functor.Initial.homToLift F X)).symm

lemma restrict_extend (φ : (Functor.const C).obj A ⟶ F ⋙ P) : restrict F A P (extend F A P φ) = φ := by
  apply NatTrans.ext
  funext X
  change (Functor.Initial.extendCone.obj ({ pt := A, π := φ } : Cone (F ⋙ P))).π.app (F.obj X) = φ.app X
  rw [Functor.Initial.extendCone_obj_π_app' _ (𝟙 (F.obj X)), P.map_id]
  change φ.app X ≫ 𝟙 _ = φ.app X
  exact Category.comp_id _

def equivalence : ((Functor.const D).obj A ⟶ P) ≃ ((Functor.const C).obj A ⟶ F ⋙ P) where
  toFun := restrict F A P
  invFun := extend F A P
  left_inv := extend_restrict F A P
  right_inv := restrict_extend F A P

lemma bijective : Function.Bijective (restrict F A P) := (equivalence F A P).bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InitialConstantMaps
