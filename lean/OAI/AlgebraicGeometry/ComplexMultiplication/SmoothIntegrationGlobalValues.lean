import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.SheafAnyHomology

/-! # Smooth Integration Global Values -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SmoothIntegrationGlobalValues

noncomputable section

section

/-! # Actual simplex integration on the genuine smooth de Rham sheaf complex

Every component integrates actual open-domain tangent forms and then applies
the canonical sheafification unit. The constant augmentation is retained.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (Model M : Type) [NormedAddCommGroup Model] [NormedSpace ℝ Model]
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold 𝓘(ℝ, Model) ∞ M]

local notation "J" => Opens.grothendieckTopology (TopCat.of M)
local notation "A" => ModuleCat.of ℂ ℂ
local notation "P" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex Model M A
local notation "integration" => OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap Model M

/-- The genuine sheafified smooth-singular complex has abelian homology. -/
instance actualSmoothSingularSheaf_hasHomology (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model M A).HasHomology n := by
  dsimp only [AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex, AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex]
  infer_instance

instance actualSmoothSingularSheaf_hasHomology_all :
    ∀ n, (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model M A).HasHomology n :=
  fun n => actualSmoothSingularSheaf_hasHomology Model M n

/-- Actual local simplex integrals define a map of genuine smooth sheaf complexes. -/
def actualSmoothIntegrationSheaf :
    Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex Model M ⟶ AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model M A where
  f p := ⟨(integration).f p ≫ toSheafify J ((P).X p)⟩
  comm' i j hij := by
    obtain rfl := hij
    apply CategoryTheory.Sheaf.hom_ext
    rw [Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d]
    dsimp only [AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex, AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex,
      Functor.mapHomologicalComplex_obj_d]
    change ((integration).f i ≫ toSheafify J ((P).X i)) ≫
      sheafifyMap J ((P).d i (i + 1)) =
      Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheafD Model M i ≫
        ((integration).f (i + 1) ≫ toSheafify J ((P).X (i + 1)))
    have hc := (integration).comm i (i + 1)
    rw [Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d] at hc
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun η => (integration).f i ≫ η)
        (toSheafify_naturality J ((P).d i (i + 1))).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun η => η ≫ toSheafify J ((P).X (i + 1))) hc).trans
              (Category.assoc _ _ _))))

/-- Its degree-zero component is the previously proved actual point integral. -/
theorem actualSmoothIntegrationSheaf_f_zero :
    (actualSmoothIntegrationSheaf Model M).f 0 =
      AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroSheafMap Model M := by
  apply CategoryTheory.Sheaf.hom_ext
  exact congrArg (fun η => η ≫ toSheafify J ((P).X 0))
    (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap_zero Model M)

/-- The actual smooth-singular resolution with the standard complex constant coefficients. -/
def actualSmoothSingularConstantAugmentation :
    (CochainComplex.single₀ (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of M))).obj
      (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexSheafOn (TopCat.of M)) ⟶ AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model M A :=
  (CochainComplex.single₀ _).map
      (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn (TopCat.of M)).hom ≫
    AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap Model M

set_option backward.isDefEq.respectTransparency false in
/-- The actual smooth-singular constant augmentation is a quasi-isomorphism. -/
theorem actualSmoothSingularConstantAugmentation_quasiIso :
    QuasiIso (actualSmoothSingularConstantAugmentation Model M) := by
  have := AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.quasiIso_manifoldSmoothSheafResolutionMap Model M
  dsimp only [actualSmoothSingularConstantAugmentation]
  infer_instance

/-- Genuine integration retains the actual smooth de Rham constant augmentation. -/
theorem actualSmoothIntegrationSheaf_constant :
    Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation Model M ≫ actualSmoothIntegrationSheaf Model M =
      actualSmoothSingularConstantAugmentation Model M := by
  apply HomologicalComplex.from_single_hom_ext
  change (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation Model M).f 0 ≫
    (actualSmoothIntegrationSheaf Model M).f 0 = _
  rw [actualSmoothIntegrationSheaf_f_zero]
  change Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model M ≫ AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroSheafMap Model M =
    ((CochainComplex.single₀ _).map
      (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn (TopCat.of M)).hom).f 0 ≫
        (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap Model M).f 0
  rw [HomologicalComplex.single_map_f_self, AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap_f_zero]
  exact AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroSheafMap_constant_augmentation Model M

variable [FiniteDimensional ℝ Model]

set_option backward.isDefEq.respectTransparency false in
/-- The actual simplex integration map induces isomorphisms of all cohomology sheaves. -/
theorem actualSmoothIntegrationSheaf_quasiIso :
    QuasiIso (actualSmoothIntegrationSheaf Model M) := by
  have := Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation_quasiIso Model M
  have : QuasiIso (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation Model M ≫
      actualSmoothIntegrationSheaf Model M) := by
    rw [actualSmoothIntegrationSheaf_constant]
    exact actualSmoothSingularConstantAugmentation_quasiIso Model M
  exact quasiIso_of_comp_left (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation Model M)
    (actualSmoothIntegrationSheaf Model M)

end

/-! # Genuine global sheaf integration has the actual global simplex-integral values -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (Model M : Type) [NormedAddCommGroup Model] [NormedSpace ℝ Model]
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold 𝓘(ℝ, Model) ∞ M]

local notation "J" => Opens.grothendieckTopology (TopCat.of M)
local notation "P" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex Model M (ModuleCat.of ℂ ℂ)

/-- The actual sheaf map integrates an ambient global form by its genuine
smooth-simplex cochain and then applies the original sheafification unit. -/
theorem actualSmoothIntegrationSheaf_globalValues (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm Model M n) :
    (((actualSmoothIntegrationSheaf Model M).f n).hom.app (Opposite.op ⊤))
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form) =
    (toSheafify J ((P).X n)).app (Opposite.op ⊤)
      ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback Model Model (ModuleCat.of ℂ ℂ)
        (Subtype.val : (⊤ : Opens M) → M)
          (contMDiff_subtype_val (I := 𝓘(ℝ, Model)) (n := ∞))).f n
            ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap Model M).f n form)) := by
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun f : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex Model M ⟶
        AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains Model (ModuleCat.of ℂ ℂ) (⊤ : Opens M) => f.f n)
      (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration_onOpen Model (⊤ : Opens M))) form
  have hvalue :
      (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration Model (⊤ : Opens M)).f n
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form) =
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback Model Model (ModuleCat.of ℂ ℂ)
        (Subtype.val : (⊤ : Opens M) → M)
          (contMDiff_subtype_val (I := 𝓘(ℝ, Model)) (n := ∞))).f n
            ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap Model M).f n form) := by
    simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
      Analysis.DifferentialForms.Manifold.OpenDeRham.manifoldDeRhamOnOpen_f_apply] using! hp
  change (toSheafify J ((P).X n)).app (Opposite.op ⊤)
    ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration Model (⊤ : Opens M)).f n
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form)) = _
  exact congrArg ((toSheafify J ((P).X n)).app (Opposite.op ⊤)) hvalue

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SmoothIntegrationGlobalValues
