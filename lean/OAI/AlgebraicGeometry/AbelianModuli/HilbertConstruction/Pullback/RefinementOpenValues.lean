import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor

/-! # Refinement Open Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.RefinementOpenValues

noncomputable section

/-! Refining any pullback by an open immersion preserves sections wherever the inverse-image open lies in that immersion's image. The original pullback map need not be an open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackRefinementMap_app_isIso_of_preimage
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) [IsOpenImmersion a] (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (hU : g ⁻¹ᵁ U ≤ a.opensRange) :
    IsIso ((OpenPullback.Refinement.openPullbackRefinementMap a g M).app U) := by
  have h₁ : IsIso (((Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M))).app U) :=
    OpenPullback.ModuleValues.openPullbackUnit_app_isIso a ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) hU
  change IsIso (((Scheme.Modules.pushforward g).map
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M))).app U ≫
    ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward a).map
      ((Scheme.Modules.pullbackComp a g).hom.app M))).app U ≫
    ((Scheme.Modules.pushforwardComp a g).hom.app ((Scheme.Modules.pullback (a ≫ g)).obj M)).app U)
  infer_instance

theorem coefficientModulePresheafMap_app_isIso {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : R →+* Γ(X, ⊤)) {M N : X.Modules} (a : M ⟶ N) (U : X.Opens) [IsIso (a.app U)] :
    IsIso (((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map a).app (.op U)) := by
  have h := (ConcreteCategory.isIso_iff_bijective (a.app U)).mp inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.RefinementOpenValues
