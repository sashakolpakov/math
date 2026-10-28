/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/FlasqueCohomology.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueSheafCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.DerivedGlobalSections

/-! # Topological Sheaf Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafCohomology.IntrinsicCech

noncomputable section

/-! The native topological sheaf interface for genuine cohomology, flasque acyclicity, and derived global sections. -/

open _root_.CategoryTheory _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}}

abbrev toSiteSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := F

abbrev H (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type u :=
  (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).obj (toSiteSheaf F)

abbrev H.map {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    IntrinsicCech.H F n →+ IntrinsicCech.H G n := CategoryTheory.Sheaf.H.map f n

abbrev H.equiv₀ (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    IntrinsicCech.H F 0 ≃+ F.obj.obj (Opposite.op ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀ F Limits.isTerminalTop

abbrev globalSectionsFunctor (X : TopCat.{u}) :=
  HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X

instance injectiveSheaf_flasque (F : TopCat.Sheaf AddCommGrpCat.{u} X) [hF : Injective F] :
    TopCat.Sheaf.IsFlasque F :=
  @InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.injectiveSheaf_isFlasque X F hF

instance flasqueSheaf_positiveCohomology_subsingleton
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [hF : TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    Subsingleton (IntrinsicCech.H F (n + 1)) :=
  @FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity.flasqueSheaf_H_succ_subsingleton X F hF n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafCohomology.IntrinsicCech
