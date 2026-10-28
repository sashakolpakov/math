import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.FrameIsoRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechPullbackRecovery

/-! # Line Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.LineRecovery

noncomputable section

/-! A descended finite cocycle recovers the original line sheaf after
actual pullback to the inverse limit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem lineFrameOpenCocycle_on {X : Scheme.{0}} {J : Type} {M : X.Modules}
    (s : J → LineFrameAtlas.LocalLineFrame M) (a b : J) (W : X.Opens)
    (ha : W ≤ (s a).domain) (hb : W ≤ (s b).domain) :
    Open.UnitCoordinates.openUnitToRegular W (Open.TransitionCocycle.openTransitionOn (fun a => (s a).domain)
      (Open.TransitionCocycle.openCoefficientsOfRegular _ (Regular.CechFrame.lineFrameRegularCoefficients s)) b a W hb ha) =
        (s a).transition (s b) W ha hb := by
  rw [← Open.TransitionCocycle.regularCoefficientsOfOpen_on, Open.TransitionCocycle.regularCoefficientsOfOpen_ofRegular, Regular.CechFrame.lineFrameRegularCoefficients_on]

variable {I : Type} [Category.{0} I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    {i : I} {J : Type} (U : J → (D.obj i).Opens) (hU : IsOpenCover U) (k : Over i)
    (q : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map k.hom ⁻¹ᵁ U a))
    (hq : Open.TransitionCocycle.OpenTransitionCocycle (fun a => D.map k.hom ⁻¹ᵁ U a) q)

theorem inverseLimitCocycleLine_iso (M : c.pt.Modules)
    (e : ∀ a, M.restrict (c.π.app i ⁻¹ᵁ U a).ι ≅ HilbertConstruction.Line.Bundles.structureModule (c.π.app i ⁻¹ᵁ U a).toScheme)
    (he : CocycleMaps.openCoefficientsConePullback D c U k q = Open.TransitionCocycle.openCoefficientsOfRegular _
      (Regular.CechFrame.lineFrameRegularCoefficients (fun a => (⟨c.π.app i ⁻¹ᵁ U a, e a⟩ : LineFrameAtlas.LocalLineFrame M)))) :
    Nonempty ((Scheme.Modules.pullback (c.π.app k.left)).obj
      (Regular.CechFrame.regularCechLineBundle (fun a => D.map k.hom ⁻¹ᵁ U a) (Open.TransitionCocycle.regularCoefficientsOfOpen _ q)
        ((Open.TransitionCocycle.regularCoefficientsOfOpen_cocycle_iff _ q).mpr hq)
        (Regular.CechPullbackRecovery.isOpenCover_preimage (D.map k.hom) U hU)).sheaf ≅ M) := by
  let s := fun a => (⟨c.π.app i ⁻¹ᵁ U a, e a⟩ : LineFrameAtlas.LocalLineFrame M)
  apply Local.FrameIsoRecovery.exists_iso_of_localFrame_transitions (CocycleFrames.inverseLimitCocycleFrame D c U k q hq) s
    (Regular.CechPullbackRecovery.isOpenCover_preimage (c.π.app i) U hU) (fun _ => rfl)
  intro a b
  have h := CocycleFrames.inverseLimitCocycleFrame_transition D c U k q hq a b (U a ⊓ U b) inf_le_left inf_le_right
  have h' := congrArg (fun r => Open.UnitCoordinates.openUnitToRegular (c.π.app i ⁻¹ᵁ (U a ⊓ U b))
    (Open.TransitionCocycle.openTransitionOn (fun a => c.π.app i ⁻¹ᵁ U a) r b a (c.π.app i ⁻¹ᵁ (U a ⊓ U b))
      ((c.π.app i).preimage_mono inf_le_right) ((c.π.app i).preimage_mono inf_le_left))) he
  exact h.trans (h'.trans (lineFrameOpenCocycle_on s a b _ inf_le_left inf_le_right))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.LineRecovery
