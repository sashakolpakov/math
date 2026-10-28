import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.FrameEquivalence
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Integral Line Bundle Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On an integral scheme, restriction of a line-bundle section to a nonempty open is injective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {M N : Y.Modules}

theorem IntegralLineBundleRestrictions.openPullbackModuleEquiv_natural (f : X ⟶ Y) [IsOpenImmersion f]
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    {U V : Y.Opens} (h : V ≤ U) (hU : U ≤ f.opensRange) (hV : V ≤ f.opensRange)
    (s : Γ(M, U)) :
    OpenPullback.FrameEquivalence.openPullbackModuleEquiv f e V hV (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (OpenPullback.FrameEquivalence.openPullbackModuleEquiv f e U hU s) := by
  simp only [OpenPullback.FrameEquivalence.openPullbackModuleEquiv_apply]
  rw [← OpenPullback.ModuleValues.openPullbackModuleValue_restriction, ← OpenPullback.ModuleValues.openPullbackModuleValue_restriction]
  exact OpenModule.MapValues.openModuleMapValue_natural f (OpenPullback.ModuleValues.pullbackModuleRestrictionMap f e.hom) h hU hV s

theorem Line.Bundles.LineBundle.restriction_injective [IsIntegral X] (L : Line.Bundles.LineBundle X)
    {U V : X.Opens} (h : V ≤ U) [Nonempty V] :
    Function.Injective (L.sheaf.presheaf.map (homOfLE h).op) := by
  intro s t hst
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  obtain ⟨W, hxW, ⟨e⟩⟩ := L.locallyTrivial x
  let a : (Scheme.Modules.pullback W.ι).obj L.sheaf ≅
      (Scheme.Modules.pullback W.ι).obj (Line.Bundles.structureModule X) := e ≪≫ (Line.Bundles.structureModulePullbackIso W.ι).symm
  let D : X.Opens := W ⊓ U
  let E : X.Opens := D ⊓ V
  have hD : D ≤ W.ι.opensRange := by simpa only [W.opensRange_ι] using (inf_le_left : D ≤ W)
  have hE : E ≤ W.ι.opensRange := inf_le_left.trans hD
  have hDE : E ≤ D := inf_le_left
  have hDU : D ≤ U := inf_le_right
  have hEV : E ≤ V := inf_le_right
  have : Nonempty E := by
    have hnon := nonempty_preirreducible_inter D.isOpen V.isOpen
      (show (D : Set X).Nonempty from ⟨x, hxW, hx⟩)
      (show (V : Set X).Nonempty from ⟨(Classical.choice (inferInstance : Nonempty V)).val,
        (Classical.choice (inferInstance : Nonempty V)).property⟩)
    exact hnon.to_subtype
  refine ⟨D, hDU, ⟨hxW, hx⟩, ?_⟩
  apply (OpenPullback.FrameEquivalence.openPullbackModuleEquiv W.ι a D hD).injective
  apply map_injective_of_isIntegral X (homOfLE hDE)
  have he := congrArg (L.sheaf.presheaf.map (homOfLE hEV).op) hst
  have he' : L.sheaf.presheaf.map (homOfLE hDE).op
      (L.sheaf.presheaf.map (homOfLE hDU).op s) =
      L.sheaf.presheaf.map (homOfLE hDE).op (L.sheaf.presheaf.map (homOfLE hDU).op t) := by
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] using he
  exact (IntegralLineBundleRestrictions.openPullbackModuleEquiv_natural W.ι a hDE hD hE _).symm.trans
    ((congrArg (OpenPullback.FrameEquivalence.openPullbackModuleEquiv W.ι a E hE) he').trans
      (IntegralLineBundleRestrictions.openPullbackModuleEquiv_natural W.ι a hDE hD hE _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
