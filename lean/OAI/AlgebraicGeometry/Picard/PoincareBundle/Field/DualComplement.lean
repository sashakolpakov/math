import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualScalar
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualGroupHom
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ComplementaryIsogeny
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveOverQuotient

/-! # Dual Complement -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualComplement

noncomputable section

/-! The actual kernel condition constructs the dual scalar complement over an arbitrary field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (n : ℕ) (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)

include hf

/-- The source and dual complementary maps are constructed and satisfy the scalar identities needed for field descent. -/
theorem exists_complements :
    ∃ (g : B.scheme ⟶ A.scheme) (e : DA.abelian.scheme ⟶ DB.abelian.scheme),
      IsMonHom g ∧ IsMonHom e ∧ g ≫ f.hom = (𝟙 B.scheme) ^ n ∧
      DualMaps.representedDualMap (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom ≫ e =
        (𝟙 DB.abelian.scheme) ^ n := by
  have : EffectiveEpi f.hom := EffectiveOverQuotient.affine_effective f.hom
  have : EffectiveEpi (f.hom ⊗ₘ f.hom) := EffectiveOverQuotient.tensor_effective f.hom
  let g := ComplementaryIsogeny.complement f.hom n hf
  have hg : IsMonHom g := ComplementaryIsogeny.complement_isMonHom f.hom n hf
  let e := DualMaps.representedDualMap (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) g
  refine ⟨g, e, hg, DualGroupHom.isMonHom g DB DA, ComplementaryIsogeny.right_complement f.hom n hf, ?_⟩
  exact (DualMaps.representedDualMap_comp (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) g f.hom).symm.trans
      ((DualMapCongruence.representedDualMap_congr (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB))
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) _ _ (ComplementaryIsogeny.right_complement f.hom n hf)).trans
          (DualScalar.dual_scalar DB n))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualComplement
