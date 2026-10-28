import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PicardInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianProducts

/-! # Recovered Picard Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredPicardInjection.Construction

noncomputable section

/-! Field Picard injection expressed through the actual recovered
source and product maps. The product recovery also preserves multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] {Y : Scheme.{0}} (u : Y ⟶ Spec (.of k))
    [Flat u] [Surjective u] [QuasiCompact u]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : Over Y)
    (e : B ≅ (Over.pullback u).obj A.scheme)

theorem recovered_field_picard_pullback_injective :
    Function.Injective (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u B A.scheme e)) := by
  intro x y h
  apply IsogenyQuotient.Field.PicardInjection.Construction.field_abelian_picard_pullback_injective A u
  apply (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso ((Over.forget Y).mapIso e)).injective
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.hom.left _ x).symm.trans
    (h.trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.hom.left _ y))

theorem recovered_field_product_picard_pullback_injective
    {h : ℕ} (D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))) (E : Over Y)
    (eD : E ≅ (Over.pullback u).obj D.scheme) :
    Function.Injective (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u e eD)) :=
  recovered_field_picard_pullback_injective u (PELModuli.CMPoints.AbelianProducts.abelianProduct A D) (B ⊗ E)
    (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedComparison u e eD)

omit [Flat u] [Surjective u] [QuasiCompact u] in
set_option backward.isDefEq.respectTransparency false in
theorem recovered_product_multiplication [GrpObj B] [IsMonHom e.hom] :
    AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap u B A.scheme e ≫ μ[A.scheme].left =
      μ[B].left ≫ AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u B A.scheme e := by
  rw [AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap_eq, Category.assoc, Picard.PoincareBundle.Field.ProductBaseChange.multiplication]
  rw [← Category.assoc]
  have he := (congrArg Over.Hom.left (IsMonHom.mul_hom e.hom)).symm
  change (e.hom ⊗ₘ e.hom).left ≫ μ[(Over.pullback u).obj A.scheme].left =
    μ[B].left ≫ e.hom.left at he
  rw [he, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredPicardInjection.Construction
