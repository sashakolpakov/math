import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.OpenTrivialization

/-! # Pullback Unit Scalars -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PullbackUnitScalars.RingedModules

noncomputable section

/-! The canonical unit comparison for the original module pullback transports
scalar endomorphisms by the original morphism of structure sheaves. -/

open _root_.CategoryTheory Opposite

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}

def unitSectionEndomorphism (S : Sheaf J RingCat.{0})
    (r : (SheafOfModules.unit.{0} S).sections) :
    SheafOfModules.unit.{0} S ⟶ SheafOfModules.unit.{0} S :=
  (SheafOfModules.unit S).unitHomEquiv.symm r

theorem unitSectionEndomorphism_app (r : (SheafOfModules.unit.{0} S).sections)
    (X : Cᵒᵖ) (a : S.obj.obj X) :
    (unitSectionEndomorphism S r).val.app X a =
      Mul.mul (α := S.obj.obj X) a (r.val X) := rfl

variable (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)

theorem unitSectionEndomorphism_pushforward
    (r : (SheafOfModules.unit.{0} S).sections)
    (t : (SheafOfModules.unit.{0} R).sections)
    (h : ∀ X, φ.hom.app X (r.val X) = t.val (F.op.obj X)) :
    unitSectionEndomorphism S r ≫ SheafOfModules.unitToPushforwardObjUnit φ =
      SheafOfModules.unitToPushforwardObjUnit φ ≫
        (SheafOfModules.pushforward φ).map (unitSectionEndomorphism R t) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (φ.hom.app X).hom (Mul.mul (α := S.obj.obj X) a (r.val X)) =
    Mul.mul (α := R.obj.obj (F.op.obj X)) (φ.hom.app X a) (t.val (F.op.obj X))
  exact ((φ.hom.app X).hom.map_mul a (r.val X)).trans
    (congrArg (fun b : R.obj.obj (F.op.obj X) =>
      Mul.mul (α := R.obj.obj (F.op.obj X)) (φ.hom.app X a) b) (h X))

variable [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]

theorem pullbackUnitSectionEndomorphism
    (r : (SheafOfModules.unit.{0} S).sections)
    (t : (SheafOfModules.unit.{0} R).sections)
    (h : ∀ X, φ.hom.app X (r.val X) = t.val (F.op.obj X)) :
    (SheafOfModules.pullback φ).map (unitSectionEndomorphism S r) ≫
        SheafOfModules.pullbackObjUnitToUnit φ =
      SheafOfModules.pullbackObjUnitToUnit φ ≫ unitSectionEndomorphism R t := by
  apply ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  exact unitSectionEndomorphism_pushforward φ r t h

end

end OAI.AlgebraicGeometry.Comparison.Betti.PullbackUnitScalars.RingedModules
