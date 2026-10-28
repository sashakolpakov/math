import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualPoincare

/-! # Dual Picard Automorphism -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPicardAutomorphism

noncomputable section

/-! Actual Poincare duals compose contravariantly and turn a group-scheme
automorphism into its inverse dual isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

omit [AlgebraicGeometry.IsReduced S] [AlgebraicGeometry.IsNoetherian S] in
theorem dualPicardEnd_id : Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D (𝟙 A.scheme) = 𝟙 D.abelian.scheme := by
  symm
  apply DualFamilyMorphism.eq_dualPicardPullback_of_poincare D D (𝟙 A.scheme)
  rfl

theorem dualPicardEnd_comp (f h : A.scheme ⟶ A.scheme) [IsMonHom f] [IsMonHom h] :
    Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D h ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D f = Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D (f ≫ h) := by
  let df := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D f
  let dh := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D h
  apply DualFamilyMorphism.eq_dualPicardPullback_of_poincare D D (f ≫ h)
  have hf := Relative.DualPoincare.dualPicardPullback_actual_poincare_relative D D f
  have hh := Relative.DualPoincare.dualPicardPullback_actual_poincare_relative D D h
  calc
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((dh ≫ df) ⊗ₘ 𝟙 A.scheme).left D.poincare.classOf =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dh ⊗ₘ 𝟙 A.scheme).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (df ⊗ₘ 𝟙 A.scheme).left D.poincare.classOf) := by
      rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom, Category.id_comp]
    _ = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dh ⊗ₘ 𝟙 A.scheme).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ f).left D.poincare.classOf) := congrArg _ hf
    _ = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ f).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dh ⊗ₘ 𝟙 A.scheme).left D.poincare.classOf) := by
      rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
        ← Over.comp_left, ← Over.comp_left]
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    _ = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ f).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ h).left D.poincare.classOf) := congrArg _ hh
    _ = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ (f ≫ h)).left D.poincare.classOf := by
      rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom, Category.id_comp]

def inverseDualAutomorphism (e : A.scheme ≅ A.scheme) [IsMonHom e.hom] :
    D.abelian.scheme ≅ D.abelian.scheme where
  hom := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D e.inv
  inv := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D e.hom
  hom_inv_id := by simpa only [Iso.hom_inv_id, dualPicardEnd_id] using dualPicardEnd_comp D e.hom e.inv
  inv_hom_id := by simpa only [Iso.inv_hom_id, dualPicardEnd_id] using dualPicardEnd_comp D e.inv e.hom

instance inverseDualAutomorphism_isMonHom (e : A.scheme ≅ A.scheme) [IsMonHom e.hom] :
    IsMonHom (inverseDualAutomorphism D e).hom :=
  DualFamilyMorphism.dualPicardPullback_preserves_given_group D D e.inv

theorem inverseDualAutomorphism_poincare (e : A.scheme ≅ A.scheme) [IsMonHom e.hom] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((inverseDualAutomorphism D e).hom ⊗ₘ e.hom).left
      D.poincare.classOf = D.poincare.classOf := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D e.inv ⊗ₘ e.hom).left
    D.poincare.classOf = D.poincare.classOf
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.hom).left)
    (Relative.DualPoincare.dualPicardPullback_actual_poincare_relative D D e.inv)
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id] at h
  simpa only [tensorHom_id, id_whiskerRight, Over.id_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] using h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPicardAutomorphism
