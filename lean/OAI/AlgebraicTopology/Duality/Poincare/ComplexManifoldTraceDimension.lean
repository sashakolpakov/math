import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace
import OAI.AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality

/-! # Complex Manifold Trace Dimension -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension

noncomputable section

section

/-!
# Naturality of the actual complex-manifold trace

Complex C1 diffeomorphisms preserve the constructed compact-support top
trace. The proof uses genuine relative pullback, the actual evaluation
pairing, and the proved naturality of the canonical complex fundamental
class. No orientation-preservation or duality hypothesis is introduced.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N]
  [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 N]

/-- At every compact support, genuine pullback by a complex diffeomorphism
preserves evaluation on the constructed integral fundamental class. -/
theorem complexFundamentalEvaluation_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (K : Compacts N)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (K : Set N)ᶜ (2 * d)) :
    RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M)
        (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K : Set M)ᶜ
        (2 * d)
        (ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
          f.toHomeomorph.isProperMap K (2 * d) c)
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d
          (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K : Set M)
          (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K).isCompact) =
      RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of N) (K : Set N)ᶜ (2 * d) c
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (K : Set N) K.isCompact) := by
  dsimp only [ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback, ProperCompactSupportPullback.compactSupportProperStagePullback]
  erw [RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality]
  congr 1
  exact AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles.complexCompactFundamentalClass_diffeomorph f
    (f.toHomeomorph ⁻¹' (K : Set N)) (K : Set N)
    (f.toHomeomorph.isProperMap.isCompact_preimage K.isCompact) K.isCompact
    (fun _ => Iff.rfl)

/-- Actual proper pullback by a complex C1 diffeomorphism preserves top
trace on compactly supported rational cohomology. -/
theorem complexManifoldTrace_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1) :
    ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
        f.toHomeomorph.isProperMap (2 * d) ≫ ComplexManifoldTrace.complexManifoldTrace d (M := M) =
      ComplexManifoldTrace.complexManifoldTrace d (M := N) := by
  apply CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of N) (2 * d)
  intro K
  rw [← Category.assoc, ProperCompactSupportPullback.compactSupportCohomologyι_properPullback, Category.assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M)
        (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K) (2 * d)
        (ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
          f.toHomeomorph.isProperMap K (2 * d) c)) =
    ComplexManifoldTrace.complexManifoldTrace d (M := N)
      (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of N) K (2 * d) c)
  rw [ComplexManifoldTrace.complexManifoldTrace_stage_apply, ComplexManifoldTrace.complexManifoldTrace_stage_apply]
  exact complexFundamentalEvaluation_diffeomorph d f K c

theorem complexManifoldTrace_diffeomorph_apply
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (2 * d)) :
    ComplexManifoldTrace.complexManifoldTrace d (M := M)
        (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
          f.toHomeomorph.isProperMap (2 * d) c) =
      ComplexManifoldTrace.complexManifoldTrace d (M := N) c :=
  ConcreteCategory.congr_hom (complexManifoldTrace_diffeomorph d f) c

/-- The equivalent statement for an actual homeomorphism with complex C1
forward and inverse maps. -/
theorem complexManifoldTrace_homeomorph (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 e)
    (hei : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 e.symm) :
    ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) e).hom
        e.isProperMap (2 * d) ≫ ComplexManifoldTrace.complexManifoldTrace d (M := M) =
      ComplexManifoldTrace.complexManifoldTrace d (M := N) := by
  let f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1 :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := he
      contMDiff_invFun := hei }
  exact complexManifoldTrace_diffeomorph d f

/-- The established homeomorphism cohomology isomorphism preserves the
same trace; this is the actual proper-pullback map. -/
theorem complexManifoldTrace_homeomorphIso (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 e)
    (hei : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 e.symm) :
    (CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
        (X := TopCat.of M) (Y := TopCat.of N) e (2 * d)).hom ≫
        ComplexManifoldTrace.complexManifoldTrace d (M := M) =
      ComplexManifoldTrace.complexManifoldTrace d (M := N) := by
  rw [← ProperCompactSupportPullback.compactSupportedCohomologyProperPullback_homeomorph]
  exact complexManifoldTrace_homeomorph d e he hei

end

/-!
# Trace transport across a proved equality of complex model dimensions

The source and target retain their native charted-space structures. A
proved equality of the numerical model dimensions supplies only the stated
degree transport; smoothness is that of the actual heterogeneous map.
The trace and compact-generator identities reduce to the established genuine
complex-diffeomorphism naturality theorems after equality elimination.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {d e : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N]
  [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 N]

/-- The actual compact fundamental classes are compatible with a
heterogeneous complex diffeomorphism and the proved equality of top degrees. -/
theorem complexCompactFundamentalClass_diffeomorph_of_dimension_eq (h : e = d)
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) M N 1)
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (hmap : ∀ x, x ∈ K ↔ f.toHomeomorph x ∈ L) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.homeomorphSupportHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
      f.toHomeomorph K L hmap (2 * d)).hom (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK) =
      eqToHom (congrArg
        (fun n => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of N) Lᶜ n)
        (congrArg (fun n => 2 * n) h)) (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass e L hL) := by
  subst e
  simpa only [eqToHom_refl, CategoryTheory.id_apply] using
    AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles.complexCompactFundamentalClass_diffeomorph f K L hK hL hmap

/-- At each actual compact support, the top evaluation pairing is invariant,
with source relative cohomology explicitly transported to its native degree. -/
theorem complexFundamentalEvaluation_diffeomorph_of_dimension_eq (h : e = d)
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) M N 1)
    (K : Compacts N)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (K : Set N)ᶜ (2 * e)) :
    RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M)
        (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K : Set M)ᶜ
        (2 * d)
        (eqToHom (congrArg
          (fun n => Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)
            (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K : Set M)ᶜ n)
          (congrArg (fun n => 2 * n) h))
          (ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
            (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
            f.toHomeomorph.isProperMap K (2 * e) c))
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d
          (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K : Set M)
          (ProperCompactSupportPullback.properCompactPreimage f.toHomeomorph f.toHomeomorph.isProperMap K).isCompact) =
      RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of N) (K : Set N)ᶜ (2 * e) c
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass e (K : Set N) K.isCompact) := by
  subst e
  simpa only [eqToHom_refl, CategoryTheory.id_apply, ModuleCat.hom_id, LinearMap.id_apply] using
    complexFundamentalEvaluation_diffeomorph d f K c

/-- Proper pullback by the actual heterogeneous complex diffeomorphism
preserves trace after the explicit transport of source cohomological degree. -/
theorem complexManifoldTrace_diffeomorph_of_dimension_eq (h : e = d)
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) M N 1) :
    ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
        f.toHomeomorph.isProperMap (2 * e) ≫
      eqToHom (congrArg
        (fun n => CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
        (congrArg (fun n => 2 * n) h)) ≫
      ComplexManifoldTrace.complexManifoldTrace d (M := M) = ComplexManifoldTrace.complexManifoldTrace e (M := N) := by
  subst e
  simpa only [eqToHom_refl, Category.id_comp] using complexManifoldTrace_diffeomorph d f

/-- The elementwise trace transport formula with the same exact degree cast. -/
theorem complexManifoldTrace_diffeomorph_of_dimension_eq_apply (h : e = d)
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) M N 1)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (2 * e)) :
    ComplexManifoldTrace.complexManifoldTrace d (M := M)
        (eqToHom (congrArg
          (fun n => CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
          (congrArg (fun n => 2 * n) h))
          (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
            (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
            f.toHomeomorph.isProperMap (2 * e) c)) =
      ComplexManifoldTrace.complexManifoldTrace e (M := N) c :=
  ConcreteCategory.congr_hom (complexManifoldTrace_diffeomorph_of_dimension_eq h f) c

/-- The same transport for a genuine homeomorphism with heterogeneous
complex C1 forward and inverse maps. -/
theorem complexManifoldTrace_homeomorph_of_dimension_eq (h : e = d)
    (u : M ≃ₜ N)
    (hu : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) 1 u)
    (hui : ContMDiff 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 u.symm) :
    ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) u).hom
        u.isProperMap (2 * e) ≫
      eqToHom (congrArg
        (fun n => CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
        (congrArg (fun n => 2 * n) h)) ≫
      ComplexManifoldTrace.complexManifoldTrace d (M := M) = ComplexManifoldTrace.complexManifoldTrace e (M := N) := by
  subst e
  simpa only [eqToHom_refl, Category.id_comp] using complexManifoldTrace_homeomorph d u hu hui

/-- The existing homeomorphism cohomology isomorphism gives the same
trace equality, with the same explicit numerical degree transport. -/
theorem complexManifoldTrace_homeomorphIso_of_dimension_eq (h : e = d)
    (u : M ≃ₜ N)
    (hu : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) 1 u)
    (hui : ContMDiff 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 u.symm) :
    (CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
        (X := TopCat.of M) (Y := TopCat.of N) u (2 * e)).hom ≫
      eqToHom (congrArg
        (fun n => CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
        (congrArg (fun n => 2 * n) h)) ≫
      ComplexManifoldTrace.complexManifoldTrace d (M := M) = ComplexManifoldTrace.complexManifoldTrace e (M := N) := by
  subst e
  simpa only [eqToHom_refl, Category.id_comp] using
    complexManifoldTrace_homeomorphIso d u hu hui

end

end OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension
