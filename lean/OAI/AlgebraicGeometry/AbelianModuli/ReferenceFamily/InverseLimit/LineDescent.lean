import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.LineRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.FrameCover

/-! # Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.LineDescent

noncomputable section

/-! Actual algebraic line bundles descend to a finite inverse-limit
stage by descending their finite affine frame cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {I : Type} [Category.{0} I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I] [Quiver.IsThin I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
theorem exists_limit_line_stage_of_frame_cover (L : HilbertConstruction.Line.Bundles.LineBundle c.pt)
    {J : Type} [Fintype J] {i : I} (U : J → (D.obj i).Opens) (hU : IsOpenCover U)
    (h₂ : ∀ a b, IsAffineOpen (U a ⊓ U b))
    (h₃ : ∀ a b d, IsAffineOpen ((U a ⊓ U b) ⊓ U d))
    (e : ∀ a, Nonempty ((Scheme.Modules.pullback (c.π.app i ⁻¹ᵁ U a).ι).obj L.sheaf ≅
      HilbertConstruction.Line.Bundles.structureModule (c.π.app i ⁻¹ᵁ U a).toScheme)) :
    ∃ (j : I) (K : HilbertConstruction.Line.Bundles.LineBundle (D.obj j)), Nonempty ((K.pullback (c.π.app j)).sheaf ≅ L.sheaf) := by
  classical
  let g := fun a => (Scheme.Modules.restrictFunctorIsoPullback (c.π.app i ⁻¹ᵁ U a).ι).app L.sheaf ≪≫ (e a).some
  let s := fun a => (⟨c.π.app i ⁻¹ᵁ U a, g a⟩ : LineFrameAtlas.LocalLineFrame L.sheaf)
  let r := Open.TransitionCocycle.openCoefficientsOfRegular (fun a => c.π.app i ⁻¹ᵁ U a) (Regular.CechFrame.lineFrameRegularCoefficients s)
  have hr : Open.TransitionCocycle.OpenTransitionCocycle (fun a => c.π.app i ⁻¹ᵁ U a) r :=
    Open.TransitionCocycle.openCoefficientsOfRegular_cocycle _ _ (Regular.CechFrame.lineFrameRegularCoefficients_cocycle s)
  obtain ⟨k, q, hq, he⟩ := CocycleDescent.exists_limit_open_cocycle_stage D c hc U h₂ h₃ r hr
  refine ⟨k.left, Regular.CechFrame.regularCechLineBundle (fun a => D.map k.hom ⁻¹ᵁ U a) (Open.TransitionCocycle.regularCoefficientsOfOpen _ q)
    ((Open.TransitionCocycle.regularCoefficientsOfOpen_cocycle_iff _ q).mpr hq) (Regular.CechPullbackRecovery.isOpenCover_preimage (D.map k.hom) U hU), ?_⟩
  exact LineRecovery.inverseLimitCocycleLine_iso D c U hU k q hq L.sheaf g he

include hc in
theorem exists_limit_line_stage
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, IsAffineHom (pullback.diagonal (terminal.from (D.obj i)))]
    (L : HilbertConstruction.Line.Bundles.LineBundle c.pt) :
    ∃ (i : I) (K : HilbertConstruction.Line.Bundles.LineBundle (D.obj i)), Nonempty ((K.pullback (c.π.app i)).sheaf ≅ L.sheaf) := by
  obtain ⟨i, n, U, hU, ha, he⟩ := FrameCover.exists_limit_line_frame_cover_stage D c hc L
  exact exists_limit_line_stage_of_frame_cover D c hc L U hU
    (fun a b => (ha a).inf (ha b)) (fun a b d => ((ha a).inf (ha b)).inf (ha d)) he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.LineDescent
