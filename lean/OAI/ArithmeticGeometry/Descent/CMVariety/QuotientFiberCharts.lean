import OAI.ArithmeticGeometry.Descent.CMVariety.FiberSliceCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticAffineCharts
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ClosedImmersionPointTopology

/-! # Quotient Fiber Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.QuotientFiberCharts.Abelian.RelativeCharts

noncomputable section

/-!
Analytic charts on actual quotient-algebra fibers. Surjectivity of the
closed-immersion coordinate map makes every regular fiber function the
restriction of an ambient regular function. The sliced chart is therefore
analytic in both directions in the regular-evaluation sense.
-/

open Set
open scoped Classical ContDiff _root_.Manifold

variable {R A B E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [CommRing B] [Algebra ℂ B]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Construct an analytic chart on the actual affine fiber algebra from
the relative chart and the surjective coordinate map of its closed immersion. -/
theorem exists_analytic_quotient_fiber_chart
    (h : A →ₐ[ℂ] B) (hsurj : Function.Surjective h) (y₀ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) (y₀.comp h) (Prod.fst : F × E → F))
    (hforward : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates C.total)
    (hrange : Set.range (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) =
      {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x.comp (IsScalarTower.toAlgHom ℂ R A) =
        (y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)}) :
    ∃ c : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E,
      y₀ ∈ c.source ∧
      c.source = (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) ⁻¹' C.total.source ∧
      (∀ y, c y = (C.total (y.comp h)).2) ∧
      RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates c ∧
      (∀ b : B, ContDiffOn ℂ ω (fun v => c.symm v b) c.target) ∧
      c.target = {v | (C.base ((y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)), v) ∈
        C.total.target} ∧
      ∀ v ∈ c.target, (c.symm v).comp h =
        C.total.symm (C.base ((y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)), v) := by
  let x₀ := y₀.comp h
  let p := fun x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => x.comp (IsScalarTower.toAlgHom ℂ R A)
  have hmap (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ C.total.source) : p x ∈ C.base.source := by
    simpa only [C.total.left_inv hx] using C.mapsTo _ (C.total.map_source hx)
  have hproj (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ C.total.source) :
      (C.total x).1 = C.base (p x) := by
    simpa only [C.total.left_inv hx] using (C.projection _ (C.total.map_source hx)).symm
  obtain ⟨c₀, hc₀, hs₀, ht₀, hf₀, hi₀⟩ :=
    FiberSliceCharts.Abelian.exists_fiber_slice_chart p x₀ C.base C.total C.basePoint C.point hmap hproj
  let H : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B ≃ₜ {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // p x = p x₀} :=
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective h hsurj).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  have hH (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) : (H y).val = y.comp h := rfl
  have hHi (x : {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // p x = p x₀}) : (H.symm x).comp h = x.val :=
    (hH (H.symm x)).symm.trans (congrArg Subtype.val (H.apply_symm_apply x))
  let c := H.transOpenPartialHomeomorph c₀
  have hc : y₀ ∈ c.source := hc₀
  have hs : c.source = (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) ⁻¹' C.total.source := by
    change H ⁻¹' c₀.source = _
    rw [hs₀]
    rfl
  have hf (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) : c y = (C.total (y.comp h)).2 := by
    change c₀ (H y) = _
    rw [hf₀, hH]
  have hi (v : E) (hv : v ∈ c.target) :
      (c.symm v).comp h = C.total.symm (C.base (p x₀), v) := by
    change (H.symm (c₀.symm v)).comp h = _
    rw [hHi, hi₀ v hv]
  refine ⟨c, hc, hs, hf, ?_, ?_, ht₀, hi⟩
  · intro V _ _ f U hreg
    have he := hforward V (fun z => (f z).comp h) U (fun a => hreg (h a))
    have hd : U ∩ f ⁻¹' c.source = U ∩ (fun z => (f z).comp h) ⁻¹' C.total.source := by
      rw [hs]
      rfl
    rw [hd]
    exact he.snd.congr (fun z _ => hf (f z))
  · intro b
    obtain ⟨a, rfl⟩ := hsurj b
    have hpair : ContDiff ℂ ω (fun v : E => (C.base (p x₀), v)) :=
      contDiff_const.prodMk contDiff_id
    have hmem : MapsTo (fun v : E => (C.base (p x₀), v)) c.target C.total.target := by
      intro v hv
      change v ∈ c₀.target at hv
      rw [ht₀] at hv
      exact hv
    apply ((C.regularTotal a).comp hpair.contDiffOn hmem).congr
    intro v hv
    exact DFunLike.congr_fun (hi v hv) a

/-- The constructed quotient-fiber chart and inverse are smooth for the
actual native real manifold used by the fiber exponential. -/
theorem exists_native_smooth_quotient_fiber_chart
    [IsDomain B] [Algebra.Smooth ℂ B] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (h : A →ₐ[ℂ] B) (hsurj : Function.Surjective h) (y₀ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) (y₀.comp h) (Prod.fst : F × E → F))
    (hforward : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates C.total)
    (hrange : Set.range (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) =
      {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x.comp (IsScalarTower.toAlgHom ℂ R A) =
        (y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)}) :
    ∃ c : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E,
      y₀ ∈ c.source ∧
      c.source = (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) ⁻¹' C.total.source ∧
      (∀ y, c y = (C.total (y.comp h)).2) ∧
      ContMDiffOn (𝓘(ℝ, Fin (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
        (𝓘(ℝ, E)) ω c c.source ∧
      ContMDiffOn (𝓘(ℝ, E))
        (𝓘(ℝ, Fin (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)) ω c.symm c.target := by
  obtain ⟨c, hc, hs, hf, ha, hi, _, _⟩ :=
    exists_analytic_quotient_fiber_chart h hsurj y₀ C hforward hrange
  exact ⟨c, hc, hs, hf, ha.real_contMDiffOn, AnalyticAffineCharts.Abelian.RelativeCharts.inverseRegular_real_contMDiffOn c hi⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.QuotientFiberCharts.Abelian.RelativeCharts
