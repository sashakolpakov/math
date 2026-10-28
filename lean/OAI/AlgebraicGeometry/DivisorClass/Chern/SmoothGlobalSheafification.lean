import OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleGlobalSectionsForget
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SmoothSheafComparison

/-! # Smooth Global Sheafification -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothGlobalSheafification

noncomputable section

/-! Original global smooth singular cochains and their actual sheafification map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def manifoldSmoothTopSectionSheafification :
    AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) (⊤ : Opens M) ⟶
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex (⊤ : Opens M) (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)) where
  f n := (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
    ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n)).app (op (⊤ : Opens M))
  comm' i j _ :=
    (congrArg (fun f => f.app (op (⊤ : Opens M)))
      (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology (TopCat.of M))
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).d i j))).symm

def manifoldSmoothGlobalSheafification :
    AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M ⟶
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex (⊤ : Opens M) (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)) :=
  AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ) (Subtype.val : (⊤ : Opens M) → M)
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)) ≫ manifoldSmoothTopSectionSheafification E M

def manifoldSmoothToAbelianSections :
    (Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) ⟶
      CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M) :=
  (Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).map (manifoldSmoothGlobalSheafification E M) ≫
    (ModuleGlobalSectionsForget.moduleForgetGlobalSectionsIso ℂ (TopCat.of M) (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ))).inv

theorem manifoldSmoothGlobalSheafification_restriction :
    AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) (TopCat.of M) ≫
        ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℂ) (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
          (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)) =
      AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M ≫ manifoldSmoothGlobalSheafification E M := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  let topc := (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (Opens.inclusion' (⊤ : Opens M))).f n c
  let eta := CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
    ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n)
  have hu := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (op (⊤ : Opens M))) (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction_unit E M (ModuleCat.of ℂ ℂ) n)) topc
  have hn := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ)
      (Subtype.val : (⊤ : Opens M) → M) (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)))) c
  change (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) (⊤ : Opens M)).f n topc =
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ) (Subtype.val : (⊤ : Opens M) → M)
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞))).f n
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f n c) at hn
  exact hu.trans (congrArg (fun v => eta.app (op (⊤ : Opens M)) v) hn)

theorem manifoldSmoothToAbelianSections_restriction :
    ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℂ (TopCat.of M) (ModuleCat.of ℂ ℂ) ≫
        ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections (TopCat.of M)).mapHomologicalComplex (.up ℕ)).map (Rational.SmoothSheafComparison.complexAbelianSmoothRestriction E M) =
      (Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) ≫ manifoldSmoothToAbelianSections E M := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg (fun f => Complex.SheafForget.complexModuleForget.map (f.f n)) (manifoldSmoothGlobalSheafification_restriction E M)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothGlobalSheafification
