import OAI.AlgebraicGeometry.Comparison.Betti.SectionSheafification
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution
import OAI.AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains

/-! # Global Sheafification -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.GlobalSheafification.Integration

noncomputable section

/-! Ordinary and smooth global singular cochains map compatibly to the
actual smooth singular sheaf through their original sheafification units. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def smoothCochainsToSheafSections : AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M ⟶
    (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ))) :=
  (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections.manifoldSmoothPresheafTopIso E M (ModuleCat.of ℂ ℂ)).inv ≫
    SectionSheafification.Integration.sectionSheafification (X := TopCat.of M) (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)) ⊤

theorem singularSmoothSheafification_square :
    AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) (TopCat.of M) ≫
        ((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
          (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)) =
      AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M ≫ smoothCochainsToSheafSections E M := by
  apply HomologicalComplex.Hom.ext
  funext n
  let p := (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (Opens.inclusion' (X := TopCat.of M) (⊤ : Opens M))).f n
  let u := (toSheafify (Opens.grothendieckTopology M)
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) (TopCat.of M) n)).app (op ⊤)
  let v := (toSheafify (Opens.grothendieckTopology M)
    ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n)).app (op ⊤)
  let s := ((AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ)).f n).hom.app (op ⊤)
  let r := (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f n
  let t := (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) (⊤ : Opens M)).f n
  let q := (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ)
    (Subtype.val : (⊤ : Opens M) → M) (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞))).f n
  have hu : u ≫ s = t ≫ v := congrArg (fun f => f.app (op (⊤ : Opens M)))
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction_unit E M (ModuleCat.of ℂ ℂ) n)
  have hn : p ≫ t = r ≫ q := congrArg (fun f => f.f n)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ)
      (Subtype.val : (⊤ : Opens M) → M) (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)))
  have hq : (smoothCochainsToSheafSections E M).f n = q ≫ v := by
    unfold smoothCochainsToSheafSections
    rw [AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections.manifoldSmoothPresheafTopIso_inv]
    rfl
  change (p ≫ u) ≫ s = r ≫ (smoothCochainsToSheafSections E M).f n
  erw [hq, Category.assoc, hu, ← Category.assoc, hn, Category.assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.GlobalSheafification.Integration
