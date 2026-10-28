import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents

/-! # Associativity Fusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion

noncomputable section

/-! The two canonical ways to combine three pullbacks agree as bundle isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {W X Y Z : Scheme.{u}}

theorem modulePullback_associativity_fusion (a : W ⟶ X) (b : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b f).app M) ≪≫
        (Scheme.Modules.pullbackComp a (b ≫ f)).app M ≪≫
        (Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app M =
      (Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback f).obj M) ≪≫
        (Scheme.Modules.pullbackComp (a ≫ b) f).app M := by
  let c₁ := (Scheme.Modules.pullbackComp a (b ≫ f)).app M
  let c₂ := (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b f).app M)
  let c₃ := (Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback f).obj M)
  let c₄ := (Scheme.Modules.pullbackComp (a ≫ b) f).app M
  let c₅ := (Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app M
  have h : c₁.inv ≫ c₂.inv ≫ c₃.hom ≫ c₄.hom = c₅.hom :=
    AssociativityComponents.modulePullback_associativity_components a b f M
  have h' := congrArg (fun k => c₂.hom ≫ c₁.hom ≫ k) h
  simp only [Iso.hom_inv_id_assoc] at h'
  apply Iso.ext
  exact h'.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion
