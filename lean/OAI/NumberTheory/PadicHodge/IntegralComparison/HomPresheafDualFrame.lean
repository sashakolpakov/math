import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.DualFrame

/-! # Hom Presheaf Dual Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomPresheafDualFrame

noncomputable section

/-! A finite dual frame detects maps out of coefficient Hom after any
additive construction, in particular supported Čech total cohomology. -/
open _root_.CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type v} [Category C] (R : Type u) [CommRing R]
  (P : C ⥤ ModuleCat.{u} R) (M : ModuleCat.{u} R)

def evaluation (x : M) : HomCoefficientFunctor.homPresheaf R P M ⟶ P where
  app a := ModuleCat.ofHom (LinearMap.applyₗ (R := R) x)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

def coefficient (l : M →ₗ[R] R) : P ⟶ HomCoefficientFunctor.homPresheaf R P M where
  app a := ModuleCat.ofHom
    { toFun x := l.smulRight x
      map_add' x y := by ext m; exact smul_add _ _ _
      map_smul' r x := by ext m; exact smul_comm _ _ _ }
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro m
    exact ((P.map f).hom.map_smul (l m) x).symm

variable {ι : Type u} [Fintype ι] (b : Finite.DualFrame.Frame R M ι)

theorem reconstruct : (∑ i, evaluation R P M (b.vector i) ≫ coefficient R P M (b.coord i)) =
    𝟙 (HomCoefficientFunctor.homPresheaf R P M) := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change M →ₗ[R] P.obj a at φ
  have h := congrArg (fun y : M => φ y) (b.reconstruct x)
  simp only [NatTrans.app_sum, ModuleCat.hom_sum, LinearMap.sum_apply,
    NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply]
  change (∑ i, (b.coord i).smulRight (φ (b.vector i))) x = φ x
  simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply,
    map_sum, LinearMap.map_smul] using h

variable {D : Type*} [Category* D] [Preadditive D]
  (F : (C ⥤ ModuleCat.{u} R) ⥤ D) [F.Additive]

theorem mapped_reconstruct : (∑ i, F.map (evaluation R P M (b.vector i)) ≫
    F.map (coefficient R P M (b.coord i))) = 𝟙 (F.obj (HomCoefficientFunctor.homPresheaf R P M)) := by
  simp only [← F.map_comp]
  rw [← F.map_sum, HomPresheafDualFrame.reconstruct, F.map_id]

theorem jointly_monic {T : D} (a a' : T ⟶ F.obj (HomCoefficientFunctor.homPresheaf R P M))
    (h : ∀ i, a ≫ F.map (evaluation R P M (b.vector i)) =
      a' ≫ F.map (evaluation R P M (b.vector i))) : a = a' := by
  calc
    a = a ≫ (∑ i, F.map (evaluation R P M (b.vector i)) ≫
        F.map (coefficient R P M (b.coord i))) := by rw [mapped_reconstruct, Category.comp_id]
    _ = a' ≫ (∑ i, F.map (evaluation R P M (b.vector i)) ≫
        F.map (coefficient R P M (b.coord i))) := by
      simp only [Preadditive.comp_sum, ← Category.assoc]
      exact Finset.sum_congr rfl (fun i _ => congrArg (· ≫ F.map (coefficient R P M (b.coord i))) (h i))
    _ = a' := by rw [mapped_reconstruct, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomPresheafDualFrame
