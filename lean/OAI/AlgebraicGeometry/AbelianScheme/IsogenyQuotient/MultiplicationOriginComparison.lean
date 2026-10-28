import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearContractionInjectivity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws

/-! # Multiplication Origin Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationOriginComparison.Construction

noncomputable section

/-! Natural multiplication on a proper connected group parameter is
determined by the unit frame at the base origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

theorem multiplication_products_eq_at_unit {S : Scheme.{u}} {E A X : Over S} [GrpObj A]
    {p : E ⟶ A} {r : E ⟶ X} {L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left}
    (D F : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication p r L) {T : Over S} (a : T ⟶ E) (ha : a ≫ p = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r a a a) (hs : D.unitFrame a ha = F.unitFrame a ha) :
    D.product a a a h = F.product a a a h := by
  apply BilinearContractionInjectivity.Construction.lineBilinear_eq_of_contractLeft (D.unitFrame a ha).hom
  rw [Picard.PoincareBundle.Bilinear.ActionLaws.contraction_unit _ _ (D.unit_left a a ha h), hs]
  exact (Picard.PoincareBundle.Bilinear.ActionLaws.contraction_unit _ _ (F.unit_left a a ha h)).symm

theorem multiplication_origin_relation {S : Scheme.{u}} {E A X T : Over S}
    [GrpObj E] [GrpObj A] (p : E ⟶ A) [IsMonHom p] (r : E ⟶ X) :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r (1 : T ⟶ E) 1 1 := by
  refine ⟨?_, rfl, rfl⟩
  rw [MonObj.one_comp p, one_mul]

theorem multiplication_group_products_eq_of_origin {k : Type u} [Field k]
    {E A X : Over (Spec (.of k))} [GrpObj E] [GrpObj A]
    {p : E ⟶ A} [IsMonHom p] {r : E ⟶ X} {L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left}
    (D F : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication p r L)
    (hs : D.unitFrame (1 : 𝟙_ (Over (Spec (.of k))) ⟶ E) (MonObj.one_comp p) =
      F.unitFrame 1 (MonObj.one_comp p))
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom]
    [GeometricallyConnected T.hom] (a b c : T ⟶ E) [IsMonHom a] [IsMonHom b] [IsMonHom c]
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r a b c) : D.product a b c h = F.product a b c h := by
  have ha : η[T] ≫ a = 1 := by rw [MonObj.one_eq_one]; exact MonObj.one_comp a
  have hb : η[T] ≫ b = 1 := by rw [MonObj.one_eq_one]; exact MonObj.one_comp b
  have hc : η[T] ≫ c = 1 := by rw [MonObj.one_eq_one]; exact MonObj.one_comp c
  let h0 := multiplication_origin_relation (T := 𝟙_ (Over (Spec (.of k)))) p r
  apply @FiberBilinearRigidity.Construction.fiberBilinear_eq_of_origin k inferInstance T inferInstance inferInstance inferInstance
    inferInstance E L a b c 1 1 1 ha hb hc (D.product a b c h) (F.product a b c h)
    (D.product_isIso a b c h) (F.product_isIso a b c h)
  rw [D.product_natural η[T] a b c h 1 1 1 h0 ha hb hc,
    F.product_natural η[T] a b c h 1 1 1 h0 ha hb hc]
  exact multiplication_products_eq_at_unit D F 1 (MonObj.one_comp p) h0 hs

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationOriginComparison.Construction
