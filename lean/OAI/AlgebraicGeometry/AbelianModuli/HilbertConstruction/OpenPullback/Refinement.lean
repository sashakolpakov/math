import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport

/-! # Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement

noncomputable section

/-! Comparison maps from one open pullback to a refined open pullback, preserving adjunction units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g]

def openPullbackRefinementMap (N : Z.Modules) :
    (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj N) ⟶
      (Scheme.Modules.pushforward (f ≫ g)).obj ((Scheme.Modules.pullback (f ≫ g)).obj N) :=
  (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj N)) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackComp f g).hom.app N)) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj N)

omit [IsOpenImmersion f] [IsOpenImmersion g] in
theorem openPullbackRefinementMap_unit (N : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N ≫ openPullbackRefinementMap f g N =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app N :=
  Pullback.TensorCompositionUnits.pullbackComp_hom_unit f g N

theorem preimage_le_openRange_of_comp {U : Z.Opens} (hU : U ≤ (f ≫ g).opensRange) :
    g ⁻¹ᵁ U ≤ f.opensRange := by
  have h : g ⁻¹ᵁ U ≤ g ⁻¹ᵁ (f ≫ g).opensRange := fun x hx => hU hx
  rwa [Scheme.Hom.opensRange_comp, g.preimage_image_eq] at h

theorem openPullbackRefinementMap_app_isIso (N : Z.Modules) (U : Z.Opens)
    (hU : U ≤ (f ≫ g).opensRange) : IsIso ((openPullbackRefinementMap f g N).app U) := by
  have h₁ : IsIso (((Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj N))).app U) :=
    ModuleValues.openPullbackUnit_app_isIso f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U)
      (preimage_le_openRange_of_comp f g hU)
  let := h₁
  change IsIso (((Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj N))).app U ≫
    ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackComp f g).hom.app N))).app U ≫
      ((Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj N)).app U)
  infer_instance

def refineOpenPullbackMap {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ (Scheme.Modules.pullback (f ≫ g)).obj N :=
  (Scheme.Modules.pullbackComp f g).inv.app M ≫ (Scheme.Modules.pullback f).map φ ≫
    (Scheme.Modules.pullbackComp f g).hom.app N

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement
