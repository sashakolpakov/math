import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeNormalizationDefect

/-! # Preconnected Hecke Differences -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The Hecke trace equation holds for differences along every connected
source mapping to the moduli space, including iterated marking maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.PreconnectedHeckeDifferences_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.PreconnectedHeckeDifferences_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm

theorem Data.SphericalPELAlbaneseData.heckeEnd_preconnected_differences (t : Local.IntegralType s)
    {Y T : Over (Spec (.of K))} [PreconnectedSpace Y.left]
    (i : Y ⟶ D.space) (x y : T ⟶ Y) :
    ((x ≫ i ≫ D.albaneseMap hg) / (y ≫ i ≫ D.albaneseMap hg)) ≫
      End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hg t) =
        (x ≫ i ≫ D.albaneseTrace hg t) / (y ≫ i ≫ D.albaneseTrace hg t) := by
  have h := (D.heckeNormalizationDefect_constant hg t).differences i x y
  simp only [Data.SphericalPELAlbaneseData.heckeNormalizationDefect, GrpObj.comp_div] at h
  have he := HeckeNormalizationDefect.div_div_exchange h
  simpa only [GrpObj.div_comp, Category.assoc] using he

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
