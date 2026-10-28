import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseExt

/-! # Albanese End Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual component differences determine every integral endomorphism
of the full product Albanese, by IntegralModel's geometric generation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

theorem Data.SphericalPELAlbaneseData.endPoint_eq_app (a : D.EndK) (T : Over (Spec (.of K)))
    (z : Additive (T ⟶ D.albaneseGroup.X)) :
    D.endPoint a z = (a.app (.op T)).hom z :=
  CentralAction.AlbaneseExt.Construction.endPoint_eq_app D a T z

theorem Data.SphericalPELAlbaneseData.endPoint_add (a b : D.EndK) {T : Over (Spec (.of K))}
    (z : Additive (T ⟶ D.albaneseGroup.X)) :
    D.endPoint (a + b) z = D.endPoint a z + D.endPoint b z := by
  simp only [Data.SphericalPELAlbaneseData.endPoint_eq_app]
  rfl

theorem Data.SphericalPELAlbaneseData.endPoint_sub (a b : D.EndK) {T : Over (Spec (.of K))}
    (z : Additive (T ⟶ D.albaneseGroup.X)) :
    D.endPoint (a - b) z = D.endPoint a z - D.endPoint b z := by
  simp only [Data.SphericalPELAlbaneseData.endPoint_eq_app]
  rfl

theorem Data.SphericalPELAlbaneseData.endPoint_one {T : Over (Spec (.of K))}
    (z : Additive (T ⟶ D.albaneseGroup.X)) : D.endPoint 1 z = z := by
  rw [Data.SphericalPELAlbaneseData.endPoint_eq_app]
  rfl

theorem Data.SphericalPELAlbaneseData.endPoint_mul (a b : D.EndK) {T : Over (Spec (.of K))}
    (z : Additive (T ⟶ D.albaneseGroup.X)) :
    D.endPoint (a * b) z = D.endPoint a (D.endPoint b z) := by
  change Additive.ofMul (z.toMul ≫ End.endSchemeMap D.albaneseGroup.X (a * b)) =
    Additive.ofMul ((z.toMul ≫ End.endSchemeMap D.albaneseGroup.X b) ≫ End.endSchemeMap D.albaneseGroup.X a)
  rw [BaseChange.endSchemeMap_mul, Category.assoc]

theorem Data.SphericalPELAlbaneseData.end_eq_of_component_differences (a b : D.EndK)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (c : Spec (.of k) ⟶ Spec (.of K))
      (j : Fin D.componentCount) (x y : Over.mk c ⟶ D.componentGeneric j),
      D.endPoint a (D.aPoint hg j x - D.aPoint hg j y) =
        D.endPoint b (D.aPoint hg j x - D.aPoint hg j y)) : a = b := by
  have he : a - b + 1 = (1 : D.EndK) :=
    CentralAction.AlbaneseExt.Construction.albanese_end_eq_one_of_differences D hg (a - b + 1) (by
      intro k _ _ c j x y
      rw [D.endPoint_add, D.endPoint_sub, D.endPoint_one, h k c j x y, sub_self, zero_add])
  exact sub_eq_zero.mp ((add_left_inj (1 : D.EndK)).mp (he.trans (zero_add _).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
