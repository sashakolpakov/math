import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ProductLineDescent
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.QuotientPoincarePullback
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualQuotientPolarization

/-! # Quotient Poincare Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.QuotientPoincareDescent

noncomputable section

/-! The quotient comparison preserves the raw Poincare line bundle.
This is proved by normalized descent of the actual comparison, rather
than imposed as a compatibility hypothesis on the quotient isomorphism. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

variable {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] {g N n : ℕ}
  {P Q : TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}

def QuotientPoincareCompatible
    (P Q : TateComparison.PEL.PELFamilyData R g N (Spec (.of k)))
    (e : Q.abelian.scheme ≅ P.abelian.scheme) [IsMonHom e.hom] : Prop :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((DualPicard.Construction.dualUnderlyingIso Q.dual P.dual e).inv ⊗ₘ e.hom).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.dual.poincare

theorem quotient_poincare_descent
    (f : TateComparison.PELIsogenies.PELIsogeny P Q n) (b : TateComparison.PELIsogenies.PELIsogeny P P n)
    (e : Q.abelian.scheme ≅ P.abelian.scheme) [IsMonHom e.hom]
    (he : f.isogeny.hom ≫ e.hom = b.isogeny.hom)
    [Etale f.isogeny.hom.left] (hd : DualQuotientPolarization.Construction.QuotientDualCompatible P Q e) :
    QuotientPoincareCompatible P Q e := by
  let d := DualPicard.Construction.dualUnderlyingIso Q.dual P.dual e
  have hgroup : IsMonHom d.inv := hd.1
  let L := P.dual.poincare.pullback (d.inv ⊗ₘ e.hom).left
  let M := Q.dual.poincare
  have hLM := QuotientPoincarePullback.Construction.quotient_poincare_pullback f b e he
  let l := PoincareNormalization.Construction.tensorPullbackZeroNormalization d.inv e.hom P.dual.poincare
    P.dual.normalizedAtDualZero.some
  let m := Q.dual.normalizedAtDualZero.some
  have hIso : Nonempty (L.sheaf ≅ M.sheaf) :=
    ProductLineDescent.Construction.normalized_product_line_iso Q.dual.abelian P.abelian Q.abelian f.isogeny.hom L M hLM l m
  exact Quotient.sound hIso

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.QuotientPoincareDescent
