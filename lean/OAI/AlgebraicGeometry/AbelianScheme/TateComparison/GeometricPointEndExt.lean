import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseEndExt

/-! # Geometric Point End Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The supplied geometric component generation determines additive
endomorphisms of every geometric Albanese point group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.GeometricPointEndExt_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.GeometricPointEndExt_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm

theorem Data.SphericalPELAlbaneseData.geometricPointEnd_ext {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K))
    (F G : Additive (Over.mk b ⟶ D.albaneseGroup.X) →+
      Additive (Over.mk b ⟶ D.albaneseGroup.X))
    (h : ∀ (j : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric j),
      F (D.aPoint hg j x - D.aPoint hg j y) = G (D.aPoint hg j x - D.aPoint hg j y)) : F = G := by
  let H := F - G + AddMonoidHom.id _
  have hH : ∀ z, H z = z := by
    apply CentralAction.AlbaneseGeneration.Construction.albanese_point_end_eq_of_differences D hg b H
    intro j x y
    change F _ - G _ + _ = _
    rw [h, sub_self, zero_add]
    rfl
  apply AddMonoidHom.ext
  intro z
  have hz : F z - G z + z = z := hH z
  exact sub_eq_zero.mp (add_right_cancel (hz.trans (zero_add z).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
