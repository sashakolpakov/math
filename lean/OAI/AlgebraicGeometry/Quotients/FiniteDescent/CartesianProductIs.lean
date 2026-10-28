import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFunctionsIs

/-! # Cartesian Product Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs

noncomputable section

/-! Constancy of functions is invariant under the Cartesian model and
holds on a product of two constant proper integral families. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.CartesianProductFunctions

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {A X S : Scheme.{u}} (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
variable (p : X ⟶ A) (f : X ⟶ S) (t : S ⟶ Spec (.of K)) (hp : IsPullback p f a t)

include hp

theorem isIso_app (U : S.Opens) : IsIso (f.app U) := by
  have := ProductFunctionsIs.Construction.ProductFunctions.isIso_app a t U
  rw [← hp.isoPullback_hom_snd, Scheme.Hom.comp_app]
  infer_instance

omit hp in
theorem restricted_unit (hf : ∀ U : S.Opens, IsIso (f.app U)) (U : S.Opens) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  have : IsIso ((f ∣_ U).app V) := by
    rw [morphismRestrict_app]
    have := hf (U.ι ''ᵁ V)
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ((ConcreteCategory.isIso_iff_bijective ((f ∣_ U).app V)).mp this)

variable {B Y : Scheme.{u}} (b : B ⟶ Spec (.of K)) [IsIntegral B] [IsProper b]
variable (q : Y ⟶ B) (g : Y ⟶ S) (hq : IsPullback q g b t)

include hq

theorem product_app (U : S.Opens) : IsIso ((pullback.fst f g ≫ f).app U) := by
  have := isIso_app a p f t hp U
  have : IsIso ((pullback.fst f g).app (f ⁻¹ᵁ U)) :=
    isIso_app b (pullback.snd f g ≫ q) (pullback.fst f g) (f ≫ t)
      ((IsPullback.of_hasPullback f g).flip.paste_horiz hq) (f ⁻¹ᵁ U)
  rw [Scheme.Hom.comp_app]
  infer_instance

theorem product_restricted_unit (U : S.Opens) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit ((pullback.fst f g ≫ f) ∣_ U).toRingCatSheafHom) :=
  restricted_unit (pullback.fst f g ≫ f) (product_app a p f t hp b q g hq) U

end Construction.CartesianProductFunctions

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs
