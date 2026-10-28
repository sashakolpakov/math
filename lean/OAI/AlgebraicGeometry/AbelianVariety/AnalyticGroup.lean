import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! # Analytic Group -/

namespace OAI.AlgebraicGeometry.AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology

noncomputable section

/-!
# ExteriorCohomology: analytic group structure from an abelian variety

These helpers derive the product topology on actual complex-valued scheme
points from affine tensor-product characters. They then prove that the
scheme group law gives a topological group and complex and real Lie groups
on the existing analytic realization. No analytic group structure is assumed.
This supports the ongoing proof of ExteriorCohomology; the exterior-cohomology theorem is
not asserted in this file.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
open scoped _root_.Topology
open scoped MonoidalCategory TensorProduct _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

/-- The complex character of a tensor product determined by a pair of characters. -/
def affineTensorPair (A B : Type) [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (xy : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[ℂ] B) :=
  Algebra.TensorProduct.lift xy.1 xy.2 (fun _ _ => Commute.all _ _)

/-- Pairing affine characters is continuous in their ordinary evaluation topologies. -/
theorem affineTensorPair_continuous (A B : Type) [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] : Continuous (affineTensorPair A B) := by
  apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
  intro t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add]; exact hx.add hy
  | tmul a b =>
    change Continuous (fun xy : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => xy.1 a * xy.2 b)
    exact ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_fst).mul
      ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval b).comp continuous_snd)

/-- The actual scheme map from the tensor-product affine chart to a product. -/
def affineProductMap {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) :
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (A ⊗[ℂ] B) ⟶ X ⊗ Y :=
  lift
    (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[ℂ] B) Algebra.TensorProduct.includeLeft ≫ f)
    (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (A ⊗[ℂ] B) Algebra.TensorProduct.includeRight ≫ g)

/-- The algebraic product chart has the expected value on complex points. -/
theorem affineProductMap_apply {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[ℂ] B))
        (affineProductMap A B f g) (affineTensorPair A B (x, y)) =
      lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f x)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B g y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap, affineProductMap, Category.assoc, lift_fst]
    rw [← Category.assoc, ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A
      ((Algebra.TensorProduct.lift x y _).comp Algebra.TensorProduct.includeLeft) ≫ f = _
    rw [Algebra.TensorProduct.lift_comp_includeLeft]
  · simp only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap, affineProductMap, Category.assoc, lift_snd]
    rw [← Category.assoc, ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv B
      ((Algebra.TensorProduct.lift x y _).comp Algebra.TensorProduct.includeRight) ≫ g = _
    rw [Algebra.TensorProduct.lift_comp_includeRight']

/-- Pairing points is continuous on each pair of affine test spaces. -/
theorem affinePointPair_continuous {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) :
    Continuous (fun xy : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B =>
      lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f xy.1)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B g xy.2)) := by
  exact ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap
    (CommAlgCat.of ℂ (A ⊗[ℂ] B)) (affineProductMap A B f g)).comp
      (affineTensorPair_continuous A B)).congr (fun xy => affineProductMap_apply A B f g xy.1 xy.2)

/-- Affine open charts prove continuity of the global point-pairing map. -/
theorem schemePointPair_continuous (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Continuous (fun xy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => lift xy.1 xy.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x, y⟩
  obtain ⟨U, hU, u, rfl⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X x
  obtain ⟨V, hV, v, rfl⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift Y y
  have ho := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap X U hU).prodMap
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap Y V hV)
  have hc := (affinePointPair_continuous (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV)).continuousAt (x := (u, v))
  exact (ho.continuousAt_iff
    (g := fun xy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => lift xy.1 xy.2)
    (x := (u, v))).mp hc

/-- Complex points of the scheme product carry the ordinary product topology. -/
def schemePointProductHomeomorph (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y) ≃ₜ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) where
  toFun p := (p ≫ fst X Y, p ≫ snd X Y)
  invFun xy := lift xy.1 xy.2
  left_inv p := by simp
  right_inv xy := by simp
  continuous_toFun := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (fst X Y)).prodMk
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (snd X Y))
  continuous_invFun := schemePointPair_continuous X Y

/-- Analytic regular-function evaluations give analytic maps in native target charts. -/
theorem contDiffOn_affineParameterizedMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
    [IsOpenImmersion j.left] {m : ℕ}
    (u : E → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (s : Set E) (hs : IsOpen s)
    (hucont : ContinuousOn u s)
    (hu : ∀ a : A, ContDiffOn ℂ ω (fun z => u z a) s)
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B m) :
    ContDiffOn ℂ ω
      (fun z => ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (u z)))
      (s ∩ {z | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (u z) ∈
        (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f).source}) := by
  let D := s ∩ {z | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (u z) ∈
    (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f).source}
  have hD : IsOpen D := hucont.isOpen_inter_preimage hs
    ((ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f).open_source.preimage
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i))
  apply contDiffOn_pi.mpr
  intro k z hz
  have hzimage : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (u z) ∈
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j '' f.source := hz.2
  obtain ⟨y, hy, hxy⟩ := hzimage
  obtain ⟨a, ha, h, _hfac, hpoint⟩ :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j (u z) ⟨y, hxy⟩
  let v : E → B → ℂ := fun w b =>
    u w (IsLocalization.Away.sec a (h b)).1 /
      (u w a) ^ (IsLocalization.Away.sec a (h b)).2
  have hval (w : E) (hw : u w a ≠ 0) (b : B) :
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨u w, hw⟩ b = v w b :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_eval A B a h ⟨u w, hw⟩ b
  have hvat (b : B) : ContDiffAt ℂ ω (fun w => v w b) z :=
    ((hu (IsLocalization.Away.sec a (h b)).1).contDiffAt (hs.mem_nhds hz.1)).div
      (((hu a).contDiffAt (hs.mem_nhds hz.1)).pow (IsLocalization.Away.sec a (h b)).2)
      (pow_ne_zero _ ha)
  have hqz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨u z, ha⟩ = y :=
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxy.symm)
  obtain ⟨g, hg, hcoords⟩ := hf.2
  obtain ⟨b, r, hcoord⟩ := hcoords k
  have hgz : v z g ≠ 0 := by
    rw [← hval z ha g, hqz]
    exact hg y hy
  have hquot := (hvat b).div ((hvat g).pow r) (pow_ne_zero r hgz)
  apply ContDiffAt.contDiffWithinAt
  apply hquot.congr_of_eventuallyEq
  have hna : ∀ᶠ w in 𝓝 z, u w a ≠ 0 :=
    ((hu a).contDiffAt (hs.mem_nhds hz.1)).continuousAt.eventually_ne ha
  filter_upwards [hD.mem_nhds hz, hna] with w hw hwa
  have hwimage : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (u w) ∈
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j '' f.source := hw.2
  obtain ⟨yw, hyw, hxyw⟩ := hwimage
  have hqw : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨u w, hwa⟩ = yw :=
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxyw.symm)
  have hqsource : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨u w, hwa⟩ ∈ f.source := hqw.symm ▸ hyw
  rw [← hpoint ⟨u w, hwa⟩, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply, hcoord _ hqsource,
    hval w hwa b, hval w hwa g]
  rfl

/-- Tensor-product evaluations are analytic in both sets of parameters. -/
theorem contDiffOn_affineTensorPair_eval
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A B : CommAlgCat ℂ) (u : E → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (v : F → Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (s : Set E) (t : Set F)
    (hu : ∀ a : A, ContDiffOn ℂ ω (fun z => u z a) s)
    (hv : ∀ b : B, ContDiffOn ℂ ω (fun z => v z b) t) (a : A ⊗[ℂ] B) :
    ContDiffOn ℂ ω (fun zw : E × F => affineTensorPair A B (u zw.1, v zw.2) a) (s ×ˢ t) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add]; exact ha.add hb
  | tmul a b =>
    change ContDiffOn ℂ ω (fun zw : E × F => u zw.1 a * v zw.2 b) (s ×ˢ t)
    exact ((hu a).comp contDiffOn_fst (fun _ h => h.1)).mul
      ((hv b).comp contDiffOn_snd (fun _ h => h.2))

/-- A scheme morphism out of a product is jointly analytic in the native regular charts. -/
theorem contDiffOn_schemePairMap_regularCharts
    {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} (φ : X ⊗ Y ⟶ Z) {n m k : ℕ}
    (c : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ))
    (d : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (Fin m → ℂ))
    (e : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) (Fin k → ℂ))
    (hc : c ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n) (hd : d ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas Y m)
    (he : e ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas Z k) :
    ContDiffOn ℂ ω
      (fun zw => e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (lift (c.symm zw.1) (d.symm zw.2))))
      ((c.target ×ˢ d.target) ∩
        {zw | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (lift (c.symm zw.1) (d.symm zw.2)) ∈ e.source}) := by
  obtain ⟨U, hU, a, ha, rfl⟩ := hc
  obtain ⟨V, hV, b, hb, rfl⟩ := hd
  obtain ⟨W, hW, c, hc, rfl⟩ := he
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V
  let C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Z W
  let f := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  let g := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV
  let j := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Z W hW
  let u := fun zw : (Fin n → ℂ) × (Fin m → ℂ) =>
    affineTensorPair A B (a.symm zw.1, b.symm zw.2)
  have hucont : ContinuousOn u (a.target ×ˢ b.target) :=
    (affineTensorPair_continuous A B).comp_continuousOn
      (a.continuousOn_symm.prodMap b.continuousOn_symm)
  have hu (t : A ⊗[ℂ] B) : ContDiffOn ℂ ω (fun z => u z t) (a.target ×ˢ b.target) :=
    contDiffOn_affineTensorPair_eval A B a.symm b.symm a.target b.target ha.1 hb.1 t
  have ht := contDiffOn_affineParameterizedMap
    (CommAlgCat.of ℂ (A ⊗[ℂ] B)) C (affineProductMap A B f g ≫ φ) j u
    (a.target ×ˢ b.target) (a.open_target.prod b.open_target) hucont hu c hc
  have hat : (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A f a).target = a.target := rfl
  have hbt : (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B g b).target = b.target := rfl
  simpa only [u, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, affineProductMap_apply,
    ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply, hat, hbt, A, B, C, f, g, j] using ht

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

/-- The algebraic translation isomorphism determined by a complex point. -/
noncomputable def pointTranslation (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) : A.toOver ≅ A.toOver :=
  GrpObj.mulRight a

/-- The algebraic translation realizes multiplication by the chosen point. -/
theorem pointTranslation_apply (a x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (pointTranslation A a).hom x = x * a := by
  have hu : SemiCartesianMonoidalCategory.toUnit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) =
      𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) := Subsingleton.elim _ _
  simp [pointTranslation, GrpObj.mulRight, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map, Hom.mul_def,
    CartesianMonoidalCategory.comp_lift_assoc, hu]

/-- Each point translation is continuous. -/
theorem continuous_point_mul_right (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    Continuous (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => x * a) := by
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (pointTranslation A a).hom).congr
    (fun x => pointTranslation_apply A a x)

/-- The algebraic inverse induces a continuous inverse on complex points. -/
theorem continuous_point_inv : Continuous (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => x⁻¹) := by
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (GrpObj.inv : A.toOver ⟶ A.toOver)).congr
    (fun x => (Hom.inv_def x).symm)

/-- Point translations are holomorphic in the existing analytic structure. -/
theorem contMDiff_point_mul_right (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, A.variety.analyticModel) 𝓘(ℂ, A.variety.analyticModel) r
      (fun x : A.variety.analyticSpace => x * a) := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (pointTranslation A a).hom r).congr
    (fun x => (pointTranslation_apply A a x).symm)

/-- Point inversion is holomorphic in the existing analytic structure. -/
theorem contMDiff_point_inv (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, A.variety.analyticModel) 𝓘(ℂ, A.variety.analyticModel) r
      (fun x : A.variety.analyticSpace => x⁻¹) := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (GrpObj.inv : A.toOver ⟶ A.toOver) r).congr
    (fun x => Hom.inv_def x)

/-- The actual complex points form a topological group under the scheme group law. -/
instance pointTopologicalGroup : IsTopologicalGroup (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) where
  continuous_mul :=
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (MonObj.mul : A.toOver ⊗ A.toOver ⟶ A.toOver)).comp
      (schemePointPair_continuous A.toOver A.toOver)).congr
        (fun xy => (Hom.mul_def xy.1 xy.2).symm)
  continuous_inv := continuous_point_inv A

/-- Multiplication is jointly holomorphic in the native analytic structure. -/
theorem contMDiff_point_mul (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, A.variety.analyticModel).prod 𝓘(ℂ, A.variety.analyticModel))
      𝓘(ℂ, A.variety.analyticModel) r
      (fun xy : A.variety.analyticSpace × A.variety.analyticSpace => xy.1 * xy.2) := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  apply contMDiff_iff.mpr
  refine ⟨continuous_mul, ?_⟩
  rintro ⟨x₁, x₂⟩ y
  have h := contDiffOn_schemePairMap_regularCharts
    (MonObj.mul : A.toOver ⊗ A.toOver ⟶ A.toOver)
    (chartAt A.variety.analyticModel x₁) (chartAt A.variety.analyticModel x₂)
    (chartAt A.variety.analyticModel y)
    (chart_mem_atlas A.variety.analyticModel x₁)
    (chart_mem_atlas A.variety.analyticModel x₂)
    (chart_mem_atlas A.variety.analyticModel y)
  simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
    PartialEquiv.prod_target, extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage, Prod.map_apply,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map, ← Hom.mul_def]
    using h.of_le (show r ≤ ω from le_top)

/-- The native complex manifold is a complex Lie group. -/
instance pointComplexLieGroup (r : ℕ∞ω) :
    LieGroup 𝓘(ℂ, A.variety.analyticModel) r A.variety.analyticSpace where
  contMDiff_mul := contMDiff_point_mul A r
  contMDiff_inv := contMDiff_point_inv A r

/-- Joint smoothness of multiplication on the underlying real manifold. -/
theorem real_contMDiff_point_mul (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, A.variety.analyticModel).prod 𝓘(ℝ, A.variety.analyticModel))
      𝓘(ℝ, A.variety.analyticModel) r
      (fun xy : A.variety.analyticSpace × A.variety.analyticSpace => xy.1 * xy.2) := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  apply contMDiff_iff.mpr
  refine ⟨continuous_mul, ?_⟩
  rintro ⟨x₁, x₂⟩ y
  have h := contDiffOn_schemePairMap_regularCharts
    (MonObj.mul : A.toOver ⊗ A.toOver ⟶ A.toOver)
    (chartAt A.variety.analyticModel x₁) (chartAt A.variety.analyticModel x₂)
    (chartAt A.variety.analyticModel y)
    (chart_mem_atlas A.variety.analyticModel x₁)
    (chart_mem_atlas A.variety.analyticModel x₂)
    (chart_mem_atlas A.variety.analyticModel y)
  simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
    PartialEquiv.prod_target, extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage, Prod.map_apply,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map, ← Hom.mul_def]
    using (h.of_le (show r ≤ ω from le_top)).restrict_scalars ℝ

/-- Smoothness of inversion on the underlying real manifold. -/
theorem real_contMDiff_point_inv (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, A.variety.analyticModel) 𝓘(ℝ, A.variety.analyticModel) r
      (fun x : A.variety.analyticSpace => x⁻¹) := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (GrpObj.inv : A.toOver ⟶ A.toOver) r).congr
    (fun x => Hom.inv_def x)

/-- The underlying real manifold is a real Lie group. -/
instance pointRealLieGroup (r : ℕ∞ω) :
    LieGroup 𝓘(ℝ, A.variety.analyticModel) r A.variety.analyticSpace where
  contMDiff_mul := real_contMDiff_point_mul A r
  contMDiff_inv := real_contMDiff_point_inv A r

end

end OAI.AlgebraicGeometry.AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology
