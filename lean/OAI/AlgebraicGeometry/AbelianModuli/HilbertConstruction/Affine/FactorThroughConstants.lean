import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Factor Through Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FactorThroughConstants

noncomputable section

/-! A morphism inducing an isomorphism on global sections has unique factorization for maps into affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}}

def affineFactorOfGlobalIso (p : X ⟶ S) [IsIso p.appTop] (f : X ⟶ Y) [IsAffine Y] : S ⟶ Y :=
  S.toSpecΓ ≫ Spec.map (f.appTop ≫ inv p.appTop) ≫ Y.isoSpec.inv

theorem affineFactorOfGlobalIso_comp (p : X ⟶ S) [IsIso p.appTop] (f : X ⟶ Y) [IsAffine Y] :
    p ≫ affineFactorOfGlobalIso p f = f := by
  unfold affineFactorOfGlobalIso
  rw [← Category.assoc p S.toSpecΓ, Scheme.toSpecΓ_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (Spec.map p.appTop), ← Spec.map_comp]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

theorem affineFactorOfGlobalIso_unique (p : X ⟶ S) [IsIso p.appTop]
    (f : X ⟶ Y) [IsAffine Y] (a : S ⟶ Y) (ha : p ≫ a = f) : a = affineFactorOfGlobalIso p f := by
  apply ext_of_isAffine
  apply (cancel_mono p.appTop).mp
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ha, affineFactorOfGlobalIso_comp]

theorem affineFactorOfGlobalIso_existsUnique (p : X ⟶ S) [IsIso p.appTop]
    (f : X ⟶ Y) [IsAffine Y] : ∃! a : S ⟶ Y, p ≫ a = f :=
  ⟨affineFactorOfGlobalIso p f, affineFactorOfGlobalIso_comp p f,
    fun a ha => affineFactorOfGlobalIso_unique p f a ha⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FactorThroughConstants
