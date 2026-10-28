import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

/-! # Analytic Product Charts -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductCharts.Constructions

noncomputable section

/-! Joint analyticity of actual maps out of a scheme product, derived from
regular affine coordinate evaluations in both source factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
open scoped _root_.Topology MonoidalCategory TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions

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
    ContDiffOn ℂ ω (fun zw : E × F => Scheme.PointProduct.Constructions.affineTensorPair A B (u zw.1, v zw.2) a) (s ×ˢ t) := by
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
    Scheme.PointProduct.Constructions.affineTensorPair A B (a.symm zw.1, b.symm zw.2)
  have hucont : ContinuousOn u (a.target ×ˢ b.target) :=
    (Scheme.PointProduct.Constructions.affineTensorPair_continuous A B).comp_continuousOn
      (a.continuousOn_symm.prodMap b.continuousOn_symm)
  have hu (t : A ⊗[ℂ] B) : ContDiffOn ℂ ω (fun z => u z t) (a.target ×ˢ b.target) :=
    contDiffOn_affineTensorPair_eval A B a.symm b.symm a.target b.target ha.1 hb.1 t
  have ht := contDiffOn_affineParameterizedMap
    (CommAlgCat.of ℂ (A ⊗[ℂ] B)) C (Scheme.PointProduct.Constructions.affineProductMap A B f g ≫ φ) j u
    (a.target ×ˢ b.target) (a.open_target.prod b.open_target) hucont hu c hc
  have hat : (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A f a).target = a.target := rfl
  have hbt : (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B g b).target = b.target := rfl
  simpa only [u, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, Scheme.PointProduct.Constructions.affineProductMap_apply,
    ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply, hat, hbt, A, B, C, f, g, j] using ht

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductCharts.Constructions
