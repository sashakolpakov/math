import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Rosati Iso Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiIsoTransport

noncomputable section

/-! Rosati compatibility is preserved by an actual polarized full-level
isomorphism intertwining the integral actions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
  {A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)

theorem poincareClass_iso_square
    (u : A.dual.abelian.scheme ⊗ A.abelian.scheme ⟶ A.dual.abelian.scheme ⊗ A.abelian.scheme)
    (v : B.dual.abelian.scheme ⊗ B.abelian.scheme ⟶ B.dual.abelian.scheme ⊗ B.abelian.scheme)
    (h : u ≫ (e.dual.hom ⊗ₘ e.abelian.hom) = (e.dual.hom ⊗ₘ e.abelian.hom) ≫ v) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.productIso.hom
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass v.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass u.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.productIso.hom v.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).symm.trans
    ((congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare))
      (congrArg Over.Hom.left h.symm)).trans
        ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp u.left e.productIso.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).trans
          (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass u.left) e.poincare)))

theorem rosati_of_polarized_iso
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (ha : ∀ a, e.abelian.hom ≫ σ.map a = ρ.map a ≫ e.abelian.hom)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation B σ := by
  intro a
  obtain ⟨q, hq, hp, hpol⟩ := hρ a
  let := hq
  let v := e.dual.inv ≫ q ≫ e.dual.hom
  have hv : e.dual.hom ≫ v = q ≫ e.dual.hom := by
    dsimp only [v]
    rw [e.dual.hom_inv_id_assoc]
  refine ⟨v, inferInstanceAs (IsMonHom (e.dual.inv ≫ q ≫ e.dual.hom)), ?_, ?_⟩
  · apply (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso e.productIso).injective
    have hl : (q ⊗ₘ 𝟙 A.abelian.scheme) ≫ (e.dual.hom ⊗ₘ e.abelian.hom) =
        (e.dual.hom ⊗ₘ e.abelian.hom) ≫ (v ⊗ₘ 𝟙 B.abelian.scheme) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hv]
    have hr : (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map a) ≫ (e.dual.hom ⊗ₘ e.abelian.hom) =
        (e.dual.hom ⊗ₘ e.abelian.hom) ≫ (𝟙 B.dual.abelian.scheme ⊗ₘ σ.map a) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, ha]
    exact (poincareClass_iso_square e _ _ hl).trans
      (hp.trans (poincareClass_iso_square e _ _ hr).symm)
  · apply (cancel_epi e.abelian.hom).mp
    rw [← Category.assoc, ← e.polarization, Category.assoc, hv,
      ← Category.assoc, hpol, Category.assoc, e.polarization,
      ← Category.assoc, ← ha, Category.assoc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiIsoTransport
