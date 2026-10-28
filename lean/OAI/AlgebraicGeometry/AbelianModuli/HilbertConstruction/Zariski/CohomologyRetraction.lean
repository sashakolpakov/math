import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyPullbackLaws

/-! # Cohomology Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyRetraction.ZariskiCohomology

noncomputable section

/-! A scheme retraction induces an injective map on actual Zariski cohomology of every module sheaf in every degree. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}}

theorem pullbackMap_injective_of_section
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (M : Y.Modules) (n : ℕ) :
    Function.Injective (CohomologyPullbackMap.ZariskiCohomology.pullbackMap f M n) := by
  intro x y hxy
  have h := congrArg (CohomologyPullbackMap.ZariskiCohomology.pullbackMap s ((Scheme.Modules.pullback f).obj M) n) hxy
  have hm := congrArg ((Cohomology.ZariskiCohomology.zariskiFunctor Y n).map ((Scheme.Modules.pullbackComp s f).hom.app M)) h
  rw [← CohomologyPullbackLaws.ZariskiCohomology.pullbackMap_comp, ← CohomologyPullbackLaws.ZariskiCohomology.pullbackMap_comp, hs] at hm
  have hi := congrArg ((Cohomology.ZariskiCohomology.zariskiFunctor Y n).map ((Scheme.Modules.pullbackId Y).hom.app M)) hm
  rw [CohomologyPullbackLaws.ZariskiCohomology.pullbackMap_id, CohomologyPullbackLaws.ZariskiCohomology.pullbackMap_id] at hi
  exact hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyRetraction.ZariskiCohomology
