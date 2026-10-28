import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity

/-! # Functions From Affine Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsFromAffineFactorization

noncomputable section

/-! Factorization of the canonical affinization map through a section identifies all global functions with base functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem globalFunctions_isIso_of_affinization_factorization
    {X S : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 _)
    (h : X.toSpecΓ = p ≫ x ≫ X.toSpecΓ) : IsIso p.appTop := by
  have he := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc] at he
  have hxp : x.appTop ≫ p.appTop = 𝟙 _ := by
    apply (cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
    simpa only [Category.assoc, Category.comp_id] using he.symm
  have hpx : p.appTop ≫ x.appTop = 𝟙 _ :=
    (Scheme.Hom.comp_appTop x p).symm.trans
      ((congrArg Scheme.Hom.appTop hx).trans Scheme.Hom.id_appTop)
  exact ⟨⟨x.appTop, hpx, hxp⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsFromAffineFactorization
