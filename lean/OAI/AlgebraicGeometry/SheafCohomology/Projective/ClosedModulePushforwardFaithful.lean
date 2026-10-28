import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Closed Module Pushforward Faithful -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedModulePushforwardFaithful

noncomputable section

/-! Closed-immersion pushforward is faithful on actual module sheaves, so the pullback counit is epic. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

theorem closedModulePushforward_faithful {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).Faithful := by
  constructor
  intro M N a b hab
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨V, hV, heq⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp U.unop.isOpen
  let W : Y.Opens := ⟨V, hV⟩
  have hW : f ⁻¹ᵁ W = U.unop := TopologicalSpace.Opens.ext heq
  have h := congrArg (fun k => k.val.app (op W)) hab
  have hh : ∀ s : Γ(M, f ⁻¹ᵁ W), a.app (f ⁻¹ᵁ W) s = b.app (f ⁻¹ᵁ W) s :=
    fun s => ConcreteCategory.congr_hom h s
  rw [hW] at hh
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact hh s

theorem closedModulePullback_counit_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  have := closedModulePushforward_faithful f
  infer_instance

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedModulePushforwardFaithful
