import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionComparison

/-! # Cartier Duality Torsion Isogeny -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionIsogeny

noncomputable section

/-! The actual polarization map is invertible on torsion of coprime
order, by CartierDuality's native isogeny theorem in every residue characteristic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f] (n : ℕ)

def nativeAbelianGroupMap : Grp.mk A.scheme ⟶ Grp.mk B.scheme := Grp.homMk f

theorem nativeTorsionPointsIso_natural :
    yonedaGrp.map (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativeAbelianGroupMap A B f) n) ≫ (CartierDualityTorsionComparison.nativeTorsionPointsIso B n).hom =
      (CartierDualityTorsionComparison.nativeTorsionPointsIso A n).hom ≫ DualityPairing.homOnTorsion A B f n := by
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change (x ≫ AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι B.scheme n =
    (x ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A.scheme n) ≫ f
  exact (Category.assoc x (AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι B.scheme n)).trans
    ((congrArg (fun q => x ≫ q) (AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion f n)).trans
      (Category.assoc x (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A.scheme n) f).symm)

theorem homOnTorsion_isIso_of_native [IsIso (AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n)] :
    IsIso (DualityPairing.homOnTorsion A B f n) := by
  have : IsMonHom (AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) :=
    AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionMap_isMonHom (nativeAbelianGroupMap A B f) n
  let e : AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) n ≅ AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk B.scheme) n :=
    Grp.mkIso' (asIso (AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n))
  have he : AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativeAbelianGroupMap A B f) n = e.hom := rfl
  have hi : IsIso (yonedaGrp.map (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativeAbelianGroupMap A B f) n)) := by
    rw [he]
    infer_instance
  have h : IsIso ((CartierDualityTorsionComparison.nativeTorsionPointsIso A n).hom ≫ DualityPairing.homOnTorsion A B f n) := by
    rw [← nativeTorsionPointsIso_natural A B f n]
    infer_instance
  exact (isIso_comp_left_iff (CartierDualityTorsionComparison.nativeTorsionPointsIso A n).hom (DualityPairing.homOnTorsion A B f n)).mp h

theorem polarizationOnTorsion_isIso {N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (n : ℕ) (hn : 0 < n)
    (hgood : n.Coprime (∏ i, δ i)) : IsIso (DualityPairing.polarizationOnTorsion P n) := by
  have hdegree (s : S) : n.Coprime (P.polarization.isogeny.hom.left.finrank
      (η[P.dual.abelian.scheme].left s)) := by
    rw [P.polarization.kernelType.degree]
    exact hgood.pow_right 2
  have : IsIso (AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap P.polarization.isogeny.hom n) :=
    AbelianScheme.CartierDuality.RelativeCoprimeTorsion.Construction.CoprimeTorsion.abelian_torsionMap_isIso P.abelian P.dual P.polarization.isogeny n hn hdegree
  exact homOnTorsion_isIso_of_native P.abelian P.dual.abelian P.polarization.isogeny.hom n

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityTorsionIsogeny
