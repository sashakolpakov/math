import OAI.AlgebraicGeometry.Picard.Homomorphisms.FunctionDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackScalars

/-! # Unit End Descent -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitEndDescent

noncomputable section

/-! Descent of scalar module endomorphisms along actual faithfully flat
scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem unitEndPullback_injective [Epi f] : Function.Injective (UnitPullbackScalars.Construction.unitEndPullback f) := by
  intro a b hab
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective Y
  apply FunctionDescent.Construction.appTop_injective_of_epi f
  exact (UnitPullbackScalars.Construction.unitEndPullback_scalar f a).symm.trans
    ((congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) hab).trans (UnitPullbackScalars.Construction.unitEndPullback_scalar f b))

theorem existsUnique_unitEnd_descent [EffectiveEpi f]
    (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))
    (ha : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f →
      UnitPullbackScalars.Construction.unitEndPullback x a = UnitPullbackScalars.Construction.unitEndPullback y a) :
    ∃! b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y), UnitPullbackScalars.Construction.unitEndPullback f b = a := by
  obtain ⟨r, hr, _⟩ := FunctionDescent.Construction.existsUnique_function_descent f (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X a) (by
    intro T x y hxy
    exact (UnitPullbackScalars.Construction.unitEndPullback_scalar x a).symm.trans
      ((congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) (ha x y hxy)).trans (UnitPullbackScalars.Construction.unitEndPullback_scalar y a)))
  let b := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv Y).symm r
  have hb : AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y b = r := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv Y).apply_symm_apply r
  have hfb : UnitPullbackScalars.Construction.unitEndPullback f b = a := by
    apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X
    exact (UnitPullbackScalars.Construction.unitEndPullback_scalar f b).trans ((congrArg f.appTop hb).trans hr)
  exact ⟨b, hfb, fun b' hb' => unitEndPullback_injective f (hb'.trans hfb.symm)⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitEndDescent
