import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Affine Families M -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineFamiliesM.Constructions.AffineFamilies

noncomputable section

/-!
# DegreeTwo: regular families in native scheme charts

A parameterized family of affine characters is analytic when every regular
function evaluates analytically. Actual maps of schemes preserve this
property in the native manifold charts, by localization and regular chart
coordinates. This applies to tensor-product families for group multiplication.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.Topology

section

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

omit [NormedSpace ℂ W] in
/-- The evaluation topology detects continuity at a single parameter. -/
theorem continuousAt_of_eval (A : CommAlgCat ℂ)
    (p : W → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (w : W)
    (hp : ∀ a : A, ContinuousAt (fun z => p z a) w) : ContinuousAt p w := by
  apply Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coe.continuousAt_iff.mpr
  exact continuousAt_pi.mpr hp

/-- Regular-coordinate tests suffice for an affine family mapped into an
arbitrary regular chart on the target scheme. -/
theorem contDiffAt_regularChart (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
    [IsOpenImmersion j.left] {m : ℕ}
    (c : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
    (hc : c ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B m)
    (p : W → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (w : W) (hp : ContinuousAt p w)
    (heval : ∀ a : A, ContDiffAt ℂ ω (fun z => p z a) w)
    (hw : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (p w) ∈
      (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j c).source) :
    ContDiffAt ℂ ω
      (fun z => ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j c (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (p z))) w := by
  have hD : ∀ᶠ z in 𝓝 w,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (p z) ∈ (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j c).source :=
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i).continuousAt.comp hp).preimage_mem_nhds
      ((ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j c).open_source.mem_nhds hw)
  apply contDiffAt_pi.mpr
  intro k
  obtain ⟨y, hy, hxy⟩ := hw
  obtain ⟨a, ha, h, _hfac, hpoint⟩ :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j (p w) ⟨y, hxy⟩
  let v : W → B → ℂ := fun z b =>
    p z (IsLocalization.Away.sec a (h b)).1 /
      (p z a) ^ (IsLocalization.Away.sec a (h b)).2
  have hval (z : W) (hz : p z a ≠ 0) (b : B) :
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨p z, hz⟩ b = v z b :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_eval A B a h ⟨p z, hz⟩ b
  have hvat (b : B) : ContDiffAt ℂ ω (fun z => v z b) w :=
    (heval (IsLocalization.Away.sec a (h b)).1).div
      ((heval a).pow (IsLocalization.Away.sec a (h b)).2) (pow_ne_zero _ ha)
  have hqw : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨p w, ha⟩ = y :=
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxy.symm)
  obtain ⟨g, hg, hcoords⟩ := hc.2
  obtain ⟨b, r, hcoord⟩ := hcoords k
  have hgw : v w g ≠ 0 := by
    rw [← hval w ha g, hqw]
    exact hg y hy
  apply ((hvat b).div ((hvat g).pow r) (pow_ne_zero r hgw)).congr_of_eventuallyEq
  have hna : ∀ᶠ z in 𝓝 w, p z a ≠ 0 := (heval a).continuousAt.eventually_ne ha
  filter_upwards [hD, hna] with z hz hza
  obtain ⟨yz, hyz, hxyz⟩ := hz
  have hqz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨p z, hza⟩ = yz :=
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxyz.symm)
  have hqsource : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨p z, hza⟩ ∈ c.source := hqz.symm ▸ hyz
  rw [← hpoint ⟨p z, hza⟩, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply, hcoord _ hqsource,
    hval z hza b, hval z hza g]
  rfl

variable [IsIntegral Y.left] [Smooth Y.hom]

/-- Evaluation-analytic affine families give analytic maps into the actual
native manifold of a smooth integral scheme. -/
theorem contMDiffAt_native (A : CommAlgCat ℂ) (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y)
    (p : W → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (w : W) (hp : ContinuousAt p w)
    (heval : ∀ a : A, ContDiffAt ℂ ω (fun z => p z a) w) :
    ContMDiffAt (𝓘(ℂ, W))
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)) ω
      (fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (p z)) w := by
  let F := fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (p z)
  let N := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ
  apply contMDiffAt_iff_target.mpr
  refine ⟨(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i).continuousAt.comp hp, ?_⟩
  have hc := chart_mem_atlas N (F w)
  obtain ⟨U, hU, c, hc, he⟩ := hc
  have hw : F w ∈ (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y U)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y U hU) c).source := by
    rw [← he]
    exact mem_chart_source N (F w)
  have h := contDiffAt_regularChart A (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y U) i
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y U hU) c hc p w hp heval hw
  have heq : (extChartAt (𝓘(ℂ, N)) (F w) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y → N) =
      ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y U hU) c := by
    change (chartAt N (F w) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y → N) = _
    rw [he]
  rw [heq]
  exact h.contMDiffAt

end

open _root_.CategoryTheory.CartesianMonoidalCategory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

variable (A B : CommAlgCat ℂ)

/-- A pair of affine complex points is an actual character of the tensor
product algebra. -/
def tensorPoint (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[ℂ] B) :=
  Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorPoint_tmul (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (a : A) (b : B) : tensorPoint A B x y (a ⊗ₜ[ℂ] b) = x a * y b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- Tensoring characters is continuous for the actual evaluation topologies. -/
theorem tensorPoint_continuous :
    Continuous (fun p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B =>
      tensorPoint A B p.1 p.2) := by
  apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorPoint_tmul]
    exact (((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_fst).mul
      ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval b).comp continuous_snd)).congr fun _ => rfl
  | add a b ha hb =>
    simp only [map_add]
    exact (ha.add hb).congr fun _ => rfl

/-- Every regular function on the tensor product evaluates analytically in
two evaluation-analytic families. -/
theorem tensorPoint_contDiffAt_eval
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (p : W → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (q : W → Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (w : W)
    (hp : ∀ a, ContDiffAt ℂ ω (fun z => p z a) w)
    (hq : ∀ b, ContDiffAt ℂ ω (fun z => q z b) w) (t : A ⊗[ℂ] B) :
    ContDiffAt ℂ ω (fun z => tensorPoint A B (p z) (q z) t) w := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simpa only [tensorPoint_tmul] using (hp a).mul (hq b)
  | add a b ha hb => simpa only [map_add] using ha.add hb

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The actual scheme map from a tensor algebra into a product of schemes. -/
def affineTensorMap (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (A ⊗[ℂ] B) ⟶ X ⊗ Y :=
  lift (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[ℂ] B) Algebra.TensorProduct.includeLeft ≫ i)
    (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (A ⊗[ℂ] B) Algebra.TensorProduct.includeRight ≫ j)

/-- The tensor-algebra family has exactly the intended pair of native
scheme-valued points. -/
theorem affineTensorMap_apply (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[ℂ] B))
        (affineTensorMap A B i j) (tensorPoint A B x y) =
      lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y) := by
  unfold ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap affineTensorMap
  rw [comp_lift]
  congr 1
  · rw [← Category.assoc, ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    congr 2
    exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  · rw [← Category.assoc, ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    congr 2
    exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineFamiliesM.Constructions.AffineFamilies
