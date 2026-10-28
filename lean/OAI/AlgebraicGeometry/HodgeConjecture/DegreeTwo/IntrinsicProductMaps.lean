import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineFamiliesM
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianTranslationsM
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! # Intrinsic Product Maps -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps

noncomputable section

/-!
# DegreeTwo: native analyticity of maps from scheme products

The product of the native manifolds is parameterized by tensor-algebra
characters in affine charts. This proves joint analyticity directly on the
existing product manifold, without adding a product-comparison assumption.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.Topology TensorProduct _root_.CategoryTheory.MonObj

namespace Constructions

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineFamiliesM.Constructions.AffineFamilies

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom]

local notation "MX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "MY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
local notation "MZ" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Z.hom) → ℂ)

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
/-- A map of schemes is analytic in the product of two affine regular charts. -/
theorem contMDiffAt_affine_product (φ : X ⊗ Y ⟶ Z)
    (A B : CommAlgCat ℂ) (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) {n m : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (d : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (hd : d ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B m)
    (w : (Fin n → ℂ) × (Fin m → ℂ)) (hw₁ : w.1 ∈ e.target) (hw₂ : w.2 ∈ d.target) :
    ContMDiffAt (𝓘(ℂ, (Fin n → ℂ) × (Fin m → ℂ))) (𝓘(ℂ, MZ)) ω
      (fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
        (lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z.1))
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (d.symm z.2)))) w := by
  let fam : (Fin n → ℂ) × (Fin m → ℂ) → Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[ℂ] B) :=
    fun z => AffineFamiliesM.Constructions.AffineFamilies.tensorPoint A B (e.symm z.1) (d.symm z.2)
  have ha (a : A) : ContDiffAt ℂ ω (fun z : (Fin n → ℂ) × (Fin m → ℂ) => e.symm z.1 a) w :=
    ((he.1 a).contDiffAt (e.open_target.mem_nhds hw₁)).fst''
  have hb (b : B) : ContDiffAt ℂ ω (fun z : (Fin n → ℂ) × (Fin m → ℂ) => d.symm z.2 b) w :=
    ((hd.1 b).contDiffAt (d.open_target.mem_nhds hw₂)).snd''
  have hc : ContinuousAt fam w := AffineFamiliesM.Constructions.AffineFamilies.continuousAt_of_eval
    (CommAlgCat.of ℂ (A ⊗[ℂ] B)) fam w
    (fun t => (AffineFamiliesM.Constructions.AffineFamilies.tensorPoint_contDiffAt_eval A B _ _ w ha hb t).continuousAt)
  have hf := AffineFamiliesM.Constructions.AffineFamilies.contMDiffAt_native (CommAlgCat.of ℂ (A ⊗[ℂ] B))
    (AffineFamiliesM.Constructions.AffineFamilies.affineTensorMap A B i j ≫ φ) fam w hc
    (AffineFamiliesM.Constructions.AffineFamilies.tensorPoint_contDiffAt_eval A B _ _ w ha hb)
  have heq : (fun z : (Fin n → ℂ) × (Fin m → ℂ) => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ (A ⊗[ℂ] B)) (AffineFamiliesM.Constructions.AffineFamilies.affineTensorMap A B i j ≫ φ) (fam z)) =
      (fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
        (lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z.1))
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (d.symm z.2)))) := by
    funext z
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp]
    exact congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
      (AffineFamiliesM.Constructions.AffineFamilies.affineTensorMap_apply A B i j (e.symm z.1) (d.symm z.2))
  rwa [heq] at hf

/-- An actual map from a scheme product is jointly analytic on the product
of its factors' native complex manifolds. -/
theorem contMDiff_product_map (φ : X ⊗ Y ⟶ Z) :
    ContMDiff ((𝓘(ℂ, MX)).prod (𝓘(ℂ, MY))) (𝓘(ℂ, MZ)) ω
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y =>
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (lift p.1 p.2)) := by
  intro p
  let : ChartedSpace (MX × MY) (MX × MY) := chartedSpaceSelf _
  apply contMDiffAt_iff_source.mpr
  obtain ⟨U, hU, e, he, hce⟩ := chart_mem_atlas MX p.1
  obtain ⟨V, hV, d, hd, hcd⟩ := chart_mem_atlas MY p.2
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V
  let i := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  let j := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV
  let w : MX × MY := (chartAt MX p.1 p.1, chartAt MY p.2 p.2)
  have hw₁ : w.1 ∈ e.target := by
    have h := (chartAt MX p.1).map_source (mem_chart_source MX p.1)
    rw [hce] at h
    change chartAt MX p.1 p.1 ∈ e.target
    rw [hce]
    exact h
  have hw₂ : w.2 ∈ d.target := by
    have h := (chartAt MY p.2).map_source (mem_chart_source MY p.2)
    rw [hcd] at h
    change chartAt MY p.2 p.2 ∈ d.target
    rw [hcd]
    exact h
  have hf := contMDiffAt_affine_product φ A B i j e d he hd w hw₁ hw₂
  have heq : (fun z : MX × MY => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
      (lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z.1))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (d.symm z.2)))) =
      (fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
        (lift ((chartAt MX p.1).symm z.1) ((chartAt MY p.2).symm z.2))) := by
    rw [hce, hcd]
    rfl
  rw [heq] at hf
  simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
    extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, Prod.map_apply, id_eq]
    using hf.contMDiffWithinAt

theorem real_contMDiff_product_map (φ : X ⊗ Y ⟶ Z) :
    ContMDiff ((𝓘(ℝ, MX)).prod (𝓘(ℝ, MY))) (𝓘(ℝ, MZ)) ω
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y =>
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (lift p.1 p.2)) := by
  intro p
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp (contMDiff_product_map φ p)
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
    extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, Prod.map_apply, id_eq,
    ModelWithCorners.range_eq_univ] using hd.restrict_scalars ℝ

end Constructions

namespace Constructions.IntrinsicAbelianLieGroup

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

/-- The actual algebraic multiplication and inversion make the native
complex points of an abelian variety a complex Lie group. -/
instance complexLieGroup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    LieGroup (𝓘(ℂ, AbelianTranslationsM.Constructions.AbelianTranslations.Model A)) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) where
  contMDiff_mul := (contMDiff_product_map (MonObj.mul (X := A.toOver))).of_le le_top
  contMDiff_inv := AbelianTranslationsM.Constructions.AbelianTranslations.contMDiff_inv A ∞

/-- The same native point group and charts form a real Lie group. -/
instance realLieGroup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    LieGroup (𝓘(ℝ, AbelianTranslationsM.Constructions.AbelianTranslations.Model A)) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) where
  contMDiff_mul := (real_contMDiff_product_map (MonObj.mul (X := A.toOver))).of_le le_top
  contMDiff_inv := AbelianTranslationsM.Constructions.AbelianTranslations.real_contMDiff_inv A ∞

end Constructions.IntrinsicAbelianLieGroup

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps
