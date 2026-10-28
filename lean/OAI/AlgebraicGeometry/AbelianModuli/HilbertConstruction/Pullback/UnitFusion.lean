import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents

/-! # Unit Fusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitFusion

noncomputable section

/-! The canonical comparison for pullback by the identity agrees with the unit isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem modulePullback_identity_fusion (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 X) f).app M ≪≫
        (Scheme.Modules.pullbackCongr (Category.id_comp f)).app M =
      (Scheme.Modules.pullbackId X).app ((Scheme.Modules.pullback f).obj M) := by
  let c₁ := (Scheme.Modules.pullbackComp (𝟙 X) f).app M
  let c₂ := (Scheme.Modules.pullbackId X).app ((Scheme.Modules.pullback f).obj M)
  let c₃ := (Scheme.Modules.pullbackCongr (Category.id_comp f)).app M
  have h : c₁.inv ≫ c₂.hom = c₃.hom := by
    have h' := congr_app (Scheme.Modules.pseudofunctor_right_unitality f) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      eqToHom_app] at h'
    have h'' : c₁.inv ≫ c₂.hom ≫ 𝟙 _ = c₃.hom := h'
    simpa only [Category.comp_id] using h''
  have h' := congrArg (fun k => c₁.hom ≫ k) h
  simp only [Iso.hom_inv_id_assoc] at h'
  apply Iso.ext
  exact h'.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitFusion
