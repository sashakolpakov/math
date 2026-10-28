import OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSmoothGlobalUnit
import OAI.AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains

/-! # Concrete Singular Global Restriction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSingularGlobalRestriction

noncomputable section

/-! # Ordinary and smooth global cochains commute with genuine sheafification -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains
open scoped _root_.Manifold ContDiff

variable (Model M : Type) [NormedAddCommGroup Model] [NormedSpace ℝ Model]
  [TopologicalSpace M] [ChartedSpace Model M]

local notation "J" => Opens.grothendieckTopology (TopCat.of M)
local notation "A" => ModuleCat.of ℂ ℂ
local notation "P" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex Model M A
local notation "Q" => OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)
local notation "Γ" => OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSmoothGlobalUnit.actualSmoothGlobalSectionsFunctor M

/-- Global sections of the actual restriction to smooth singular simplices. -/
def actualOrdinaryToSmoothGlobalSheafRestriction :
    AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections A (TopCat.of M) ⟶
      ConcreteSmoothGlobalUnit.actualSmoothSingularGlobalComplex Model M :=
  (Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)).map
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction Model M A)

set_option backward.isDefEq.respectTransparency false in
/-- Restricting actual ordinary cochains commutes with both actual global units. -/
theorem actualSingularGlobalRestriction_square :
    AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections A (TopCat.of M) ≫
        actualOrdinaryToSmoothGlobalSheafRestriction Model M =
      AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction Model A M ≫
        ConcreteSmoothGlobalUnit.actualSmoothCochainsToGlobalSheafSections Model M := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hu : (toSheafify J ((Q).X n)).app (Opposite.op ⊤) ≫
      (((AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction Model M A).f n).hom.app (Opposite.op ⊤)) =
    ((AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison.manifoldSmoothPresheafRestriction Model M A).f n).app (Opposite.op ⊤) ≫
      (toSheafify J ((P).X n)).app (Opposite.op ⊤) :=
    NatTrans.congr_app (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction_unit Model M A n) (Opposite.op ⊤)
  have hn := congrArg (fun f => f.f n)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A
      (Subtype.val : (⊤ : Opens M) → M)
      (contMDiff_subtype_val (I := 𝓘(ℝ, Model)) (n := ∞)))
  rw [HomologicalComplex.comp_f, AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections_f,
    HomologicalComplex.comp_f, ConcreteSmoothGlobalUnit.actualSmoothCochainsToGlobalSheafSections_f]
  change ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A (Opens.inclusion' (⊤ : Opens (TopCat.of M)))).f n ≫
    (toSheafify J ((Q).X n)).app (Opposite.op ⊤)) ≫
      (((AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction Model M A).f n).hom.app (Opposite.op ⊤)) = _
  rw [Category.assoc, hu, ← Category.assoc]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using!
    congrArg (fun f => f ≫ (toSheafify J ((P).X n)).app (Opposite.op ⊤)) hn

/-- The same square holds on actual global cohomology in every degree. -/
theorem actualSingularGlobalRestriction_homology_square (n : ℕ) :
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections A (TopCat.of M)) n ≫
        HomologicalComplex.homologyMap (actualOrdinaryToSmoothGlobalSheafRestriction Model M) n =
      HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction Model A M) n ≫
        HomologicalComplex.homologyMap (ConcreteSmoothGlobalUnit.actualSmoothCochainsToGlobalSheafSections Model M) n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    actualSingularGlobalRestriction_square]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSingularGlobalRestriction
