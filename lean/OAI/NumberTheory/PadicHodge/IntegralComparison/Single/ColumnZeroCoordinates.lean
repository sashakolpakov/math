import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowZeroCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal

/-! # Column Zero Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnZeroCoordinates

noncomputable section

/-! Exact lowest-degree coordinates for the original single-column
comparison, including the total-flip sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable {D : Type u} [Category.{v} D] [Abelian D] [HasCoproducts.{0} D]

theorem flip_projection (B : HomologicalComplex₂ D (.up ℕ) (.up ℕ)) (c : ℕ) :
    (B.totalFlipIso (.up ℕ)).inv.f (0+c) ≫
      AbelianSingleRowTotal.projection B.flip 0 c (0+c) rfl =
    AbelianSingleRowTotal.projection B c 0 (0+c) (by omega) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [← Category.assoc, B.ιTotal_totalFlipIso_f_inv]
  by_cases hp : p = c
  · subst p
    have hq : q = 0 := by change c + q = 0 + c at hpq; omega
    subst q
    have hs : ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c 0 = 1 := by
      change ((c : ℤ) * (0 : ℤ)).negOnePow = 1
      simp
    simp [AbelianSingleRowTotal.projection, hs]
  · simp [AbelianSingleRowTotal.projection, hp]

variable {C : Type w} [Category.{z} C] [Abelian C]
  (F : C ⥤ CochainComplex D ℕ) [F.Additive] (M : C) (c : ℕ)

theorem coordinate :
    ((Functor.SingleTotal.bicomplex F M c).total (.up ℕ)).homologyπ (0+c) ≫
      (Functor.SingleTotal.homologyIso F M c 0).hom ≫
        (CochainComplex.isoHomologyπ₀ (F.obj M)).inv ≫ (F.obj M).iCycles 0 =
    ((Functor.SingleTotal.bicomplex F M c).total (.up ℕ)).iCycles (0+c) ≫
      AbelianSingleRowTotal.projection (Functor.SingleTotal.bicomplex F M c)
        c 0 (0+c) (by omega) ≫ (Functor.SingleTotal.rowIso F M c).hom.f 0 := by
  let B := Functor.SingleTotal.bicomplex F M c
  let e := B.totalFlipIso (.up ℕ)
  have hf := homologyπ_naturality e.inv (0+c)
  have hr := RowZeroCoordinates.coordinate B.flip c
    (Functor.SingleTotal.off_degree F M c)
  have hz := RowZeroCoordinates.zero_map (Functor.SingleTotal.rowIso F M c).hom
  change (B.total (.up ℕ)).homologyπ (0+c) ≫
    (homologyMap e.inv (0+c) ≫
      (AbelianSingleRowTotal.homologyIso B.flip c (Functor.SingleTotal.off_degree F M c) 0).hom ≫
      homologyMap (Functor.SingleTotal.rowIso F M c).hom 0) ≫ _ ≫ _ = _
  calc
    _ = (cyclesMap e.inv (0+c) ≫
        (B.flip.total (.up ℕ)).homologyπ (0+c) ≫
        (AbelianSingleRowTotal.homologyIso B.flip c (Functor.SingleTotal.off_degree F M c) 0).hom ≫
        (CochainComplex.isoHomologyπ₀ (B.X c)).inv ≫ (B.X c).iCycles 0) ≫
          (Functor.SingleTotal.rowIso F M c).hom.f 0 := by
      rw [Category.assoc, Category.assoc, hz]
      simp only [← Category.assoc]
      rw [hf]
    _ = (cyclesMap e.inv (0+c) ≫ (B.flip.total (.up ℕ)).iCycles (0+c) ≫
        AbelianSingleRowTotal.projection B.flip 0 c (0+c) rfl) ≫
          (Functor.SingleTotal.rowIso F M c).hom.f 0 := by
      exact congrArg (fun a => (cyclesMap e.inv (0+c) ≫ a) ≫
        (Functor.SingleTotal.rowIso F M c).hom.f 0) hr
    _ = _ := by
      rw [← Category.assoc, cyclesMap_i]
      simp only [Category.assoc]
      simpa only [Category.assoc] using congrArg (fun a => (B.total (.up ℕ)).iCycles (0+c) ≫ a ≫
        (Functor.SingleTotal.rowIso F M c).hom.f 0) (flip_projection B c)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnZeroCoordinates
