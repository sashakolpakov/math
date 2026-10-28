import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization

/-! # Quotient Poincare Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.QuotientPoincarePullback.Construction

noncomputable section

/-! The raw Poincare bundles of the quotient comparison agree after
pullback by the actual quotient isogeny. This precedes normalized descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {R : Type u} [CommRing R] {g N n m : ℕ}
  {P Q Q' : TateComparison.PEL.PELFamilyData R g N S}

/-- The two actual isogeny Poincare equations imply equality of the raw
line-bundle classes after the quotient cover, without assuming a
Poincare compatibility for the quotient isomorphism. -/
theorem quotient_poincare_pullback
    (f : TateComparison.PELIsogenies.PELIsogeny P Q n) (g : TateComparison.PELIsogenies.PELIsogeny P Q' m)
    (e : Q.abelian.scheme ≅ Q'.abelian.scheme) [IsMonHom e.hom]
    (he : f.isogeny.hom ≫ e.hom = g.isogeny.hom) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 Q.dual.abelian.scheme ⊗ₘ f.isogeny.hom).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        ((DualPicard.Construction.dualUnderlyingIso Q.dual Q'.dual e).inv ⊗ₘ e.hom).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q'.dual.poincare)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 Q.dual.abelian.scheme ⊗ₘ f.isogeny.hom).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.dual.poincare) := by
  let d := DualPicard.Construction.dualUnderlyingIso Q.dual Q'.dual e
  have hd : d.inv ≫ g.dualHom = f.dualHom := by
    rw [← DualFactorization.Construction.dual_quotient_factorization f g e he, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  have h₁ : (𝟙 Q.dual.abelian.scheme ⊗ₘ f.isogeny.hom).left ≫
      (d.inv ⊗ₘ e.hom).left =
      (d.inv ⊗ₘ 𝟙 P.abelian.scheme).left ≫
        (𝟙 Q'.dual.abelian.scheme ⊗ₘ g.isogeny.hom).left := by
    simp only [← Over.comp_left, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, he]
  have h₂ : (d.inv ⊗ₘ 𝟙 P.abelian.scheme).left ≫
      (g.dualHom ⊗ₘ 𝟙 P.abelian.scheme).left =
      (f.dualHom ⊗ₘ 𝟙 P.abelian.scheme).left := by
    rw [← Over.comp_left, tensorHom_comp_tensorHom, Category.id_comp, hd]
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (d.inv ⊗ₘ e.hom).left _) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h₁, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    g.poincare, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h₂, f.poincare]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.QuotientPoincarePullback.Construction
