import OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalFlasque
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueNatQuasiIso

/-! # Total Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalSections

noncomputable section

/-! Open sections of the functorial Godement total preserve quasi-isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

local instance godementSectionsCategoryWithHomology (X : TopCat.{0}) :
    CategoryWithHomology (TopCat.Sheaf (ModuleCat.{0} ℂ) X) :=
  inferInstanceAs (CategoryWithHomology (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)))

variable {X : TopCat.{0}}
  {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ}
  (f : K ⟶ L) (hf : QuasiIso f)

include hf

theorem godementTotalMap_quasiIso : QuasiIso (TotalNaturality.godementTotalMap f) := by
  have hK : QuasiIso (Bicomplex.godementTotalAugmentation K) := TotalQuasiIso.godementTotalAugmentation_quasiIso K
  have hL : QuasiIso (Bicomplex.godementTotalAugmentation L) := TotalQuasiIso.godementTotalAugmentation_quasiIso L
  have hc : QuasiIso (Bicomplex.godementTotalAugmentation K ≫ TotalNaturality.godementTotalMap f) := by
    rw [TotalNaturality.godementTotalAugmentation_naturality]
    exact quasiIso_comp f (Bicomplex.godementTotalAugmentation L)
  exact quasiIso_of_comp_left (Bicomplex.godementTotalAugmentation K) (TotalNaturality.godementTotalMap f)

theorem godementTotalMap_sections_quasiIso (U : Opens X) :
    QuasiIso (((FlasqueBiproduct.sections U).mapHomologicalComplex (.up ℕ)).map
      (TotalNaturality.godementTotalMap f)) :=
  FlasqueNatQuasiIso.nat_sections_quasiIso (TotalNaturality.godementTotalMap f)
    (TotalFlasque.godementTotal_isFlasque K) (TotalFlasque.godementTotal_isFlasque L) (godementTotalMap_quasiIso f hf) U

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalSections
