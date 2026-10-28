import OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham
import OAI.Analysis.DifferentialForms.Manifold.CechDeRham

/-! # Manifold Open Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration

noncomputable section

/-!
Actual integration of ambient open-domain manifold forms. The source is
transported through the proved intrinsic-open de Rham isomorphism, and the
target is the existing smooth singular cochain complex of that open manifold.
Naturality gives both a presheaf of cochain maps and a map of presheaf complexes.
The degree-zero map agrees with the already checked augmentation map.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped Simplicial _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Integrate an actual ambient-local form over smooth singular simplices
of its intrinsic open manifold. -/
def manifoldOpenIntegration (U : Opens M) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E U ⟶ Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E U).hom ≫ SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E U

@[simp]
theorem manifoldOpenIntegration_f_apply (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    (manifoldOpenIntegration E U).f n form =
      (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E U).f n
        (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n form) := rfl

/-- Evaluation is the actual signed Duffy integral of the corresponding
intrinsic form; the source transport introduces no additional choice. -/
@[simp]
theorem manifoldOpenIntegration_evaluation (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet _⦋n⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) sigma ((manifoldOpenIntegration E U).f n form) =
        SmoothSimplexIntegration.smoothSimplexIntegration sigma (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n form) :=
  SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_evaluation E U n
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n form) sigma

/-- Ambient restriction of actual forms agrees with restriction of their
integrated smooth singular cochains. -/
theorem manifoldOpenIntegration_restrict {U V : Opens M} (h : U ≤ V) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict E h ≫ manifoldOpenIntegration E U =
      manifoldOpenIntegration E V ≫
        Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E M (ModuleCat.of ℂ ℂ) (homOfLE h) := by
  change Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict E h ≫
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E U).hom ≫ SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E U) =
    ((Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E V).hom ≫ SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E V) ≫
      Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ) (Opens.inclusion h)
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h)
  rw [← Category.assoc, Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso_restrict, Category.assoc,
    SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality, ← Category.assoc]

/-- Restricting a global form before integration is pullback of its actual
global smooth singular integration cochain. -/
theorem manifoldOpenIntegration_onOpen (U : Opens M) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.manifoldDeRhamOnOpen E U ≫ manifoldOpenIntegration E U =
      SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M ≫
        Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ) (Subtype.val : U → M)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)) := by
  unfold manifoldOpenIntegration
  rw [← Category.assoc, Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso_onOpen,
    SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality]

variable (M) in
/-- The actual integration natural transformation on all ambient open domains. -/
def manifoldOpenIntegrationNat :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamPresheaf E M ⟶
      Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothCochainPresheaf E M (ModuleCat.of ℂ ℂ) where
  app U := manifoldOpenIntegration E (unop U)
  naturality _ _ h := manifoldOpenIntegration_restrict E (leOfHom h.unop)

variable (M) in
/-- Integration in one degree is a morphism of the actual module-valued
presheaves of forms and smooth singular cochains. -/
def manifoldOpenIntegrationDegree (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M n ⟶
      Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E M (ModuleCat.of ℂ ℂ) n where
  app U := (manifoldOpenIntegration E (unop U)).f n
  naturality U V h := by
    change (Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict E (leOfHom h.unop) ≫
      manifoldOpenIntegration E (unop V)).f n =
      (manifoldOpenIntegration E (unop U) ≫
        Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E M (ModuleCat.of ℂ ℂ) h.unop).f n
    exact congrArg (fun f => f.f n)
      (manifoldOpenIntegration_restrict E (leOfHom h.unop))

variable (M) in
/-- The actual de Rham-to-smooth-singular map of complexes of presheaves. -/
def manifoldOpenIntegrationPresheafMap :
    Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M ⟶
      Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ) where
  f n := manifoldOpenIntegrationDegree E M n
  comm' i j hij := by
    obtain rfl := (show i + 1 = j from hij)
    rw [Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d]
    apply NatTrans.ext
    funext U
    have h := (manifoldOpenIntegration E (unop U)).comm i (i + 1)
    rw [Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex_d] at h
    exact h

variable (M) in
@[simp]
theorem manifoldOpenIntegrationPresheafMap_f_app (n : ℕ) (U : Opens M) :
    ((manifoldOpenIntegrationPresheafMap E M).f n).app (op U) =
      (manifoldOpenIntegration E U).f n := rfl

/-- The degree-zero component is exactly the separately verified point
integration map used by the constant-sheaf augmentation square. -/
theorem manifoldOpenIntegration_zero (U : Opens M) :
    (manifoldOpenIntegration E U).f 0 =
      ModuleCat.ofHom (SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration E U) := by
  rfl

variable (M) in
/-- The full integration map and the established augmentation map have
identical degree-zero presheaf components. -/
theorem manifoldOpenIntegrationDegree_zero :
    manifoldOpenIntegrationDegree E M 0 = SmoothSimplexSheafAugmentation.smoothSimplexZeroPresheafMap E M := by
  apply NatTrans.ext
  funext U
  exact manifoldOpenIntegration_zero E (unop U)

variable (M) in
theorem manifoldOpenIntegrationPresheafMap_zero :
    (manifoldOpenIntegrationPresheafMap E M).f 0 =
      SmoothSimplexSheafAugmentation.smoothSimplexZeroPresheafMap E M :=
  manifoldOpenIntegrationDegree_zero E M

/-- Actual induced integration on cohomology of an ambient open domain. -/
def manifoldOpenIntegrationCohomology (U : Opens M) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamCohomology E U n ⟶
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U).homology n :=
  HomologicalComplex.homologyMap (manifoldOpenIntegration E U) n

/-- The actual open-domain cohomology maps commute with restriction. -/
theorem manifoldOpenIntegrationCohomology_restrict {U V : Opens M} (h : U ≤ V) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamCohomologyRestrict E h n ≫ manifoldOpenIntegrationCohomology E U n =
      manifoldOpenIntegrationCohomology E V n ≫
        HomologicalComplex.homologyMap
          (Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E M (ModuleCat.of ℂ ℂ) (homOfLE h)) n := by
  change HomologicalComplex.homologyMap (Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict E h) n ≫
      HomologicalComplex.homologyMap (manifoldOpenIntegration E U) n =
    HomologicalComplex.homologyMap (manifoldOpenIntegration E V) n ≫
      HomologicalComplex.homologyMap
        (Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E M (ModuleCat.of ℂ ℂ) (homOfLE h)) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    manifoldOpenIntegration_restrict]

variable (M) in
/-- The induced natural transformation of genuine cohomology presheaves. -/
def manifoldOpenIntegrationCohomologyNat (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamCohomologyPresheaf E M n ⟶
      Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothCohomologyPresheaf E M (ModuleCat.of ℂ ℂ) n :=
  Functor.whiskerRight (manifoldOpenIntegrationNat E M)
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) n)

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration
