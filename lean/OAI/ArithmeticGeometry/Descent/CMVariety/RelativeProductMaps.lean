import OAI.ArithmeticGeometry.Descent.CMVariety.RegularSectionCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.RelativeTensorPoints

/-! # Relative Product Maps -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Actual pairs of points in smooth relative product coordinates. Both points
lie over the same base point by the proved coordinate projection identity.
They therefore construct genuine characters of the relative tensor product,
with analytic evaluation of all its regular functions.
-/

open Set
open scoped Classical ContDiff TensorProduct

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A}

/-- The actual open domain of two points with a common base coordinate. -/
def SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.pairDomain
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F)) : Set (F × (E × E)) :=
  {z | (z.1, z.2.1) ∈ C.total.target ∧ (z.1, z.2.2) ∈ C.total.target}

theorem SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.pairDomain_isOpen
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F)) :
    IsOpen C.pairDomain :=
  (C.total.open_target.preimage (continuous_fst.prodMk continuous_snd.fst)).inter
    (C.total.open_target.preimage (continuous_fst.prodMk continuous_snd.snd))

theorem SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.pair_base_eq
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F))
    (z : F × (E × E)) (hz : z ∈ C.pairDomain) :
    (C.total.symm (z.1, z.2.1)).comp (IsScalarTower.toAlgHom ℂ R A) =
      (C.total.symm (z.1, z.2.2)).comp (IsScalarTower.toAlgHom ℂ R A) := by
  apply C.base.injOn (C.mapsTo _ hz.1) (C.mapsTo _ hz.2)
  rw [C.projection _ hz.1, C.projection _ hz.2]

/-- Construct the actual relative fiber-product family from the two inverse
product charts, proving all regular-function evaluations analytic. -/
theorem SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.exists_pairPointFamily
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F)) :
    ∃ f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A),
      (∀ z ∈ C.pairDomain, ∀ a b,
        f z (a ⊗ₜ[R] b) = C.total.symm (z.1, z.2.1) a *
          C.total.symm (z.1, z.2.2) b) ∧
      ∀ t : A ⊗[R] A, ContDiffOn ℂ ω (fun z => f z t) C.pairDomain := by
  apply RelativeTensorPoints.Abelian.RelativeCharts.exists_analytic_relativeTensorFamily
    (fun z => C.total.symm (z.1, z.2.1)) (fun z => C.total.symm (z.1, z.2.2))
    C.pairDomain C.pair_base_eq
  · intro a
    exact (C.regularTotal a).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.fst) (fun _ hz => hz.1)
  · intro a
    exact (C.regularTotal a).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.snd) (fun _ hz => hz.2)
  · exact RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl

/-- In normalized coordinates the genuine section gives a pair throughout
the constructed base neighborhood. -/
theorem RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts.section_mem_pairDomain {s : A →ₐ[ℂ] R}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s)
    (z : F) (hz : z ∈ N.neighborhood) : (z, (0, 0)) ∈ N.charts.pairDomain := by
  have h := N.charts.total.map_source (N.sectionPoint z hz)
  rw [N.sectionZero z hz] at h
  exact ⟨h, h⟩

theorem RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts.pairPointFamily_center {s : A →ₐ[ℂ] R}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s)
    (f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A))
    (hf : ∀ z ∈ N.charts.pairDomain, ∀ a b,
      f z (a ⊗ₜ[R] b) = N.charts.total.symm (z.1, z.2.1) a *
        N.charts.total.symm (z.1, z.2.2) b) :
    f (N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), (0, 0)) =
      RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint x x rfl := by
  let z₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  have hc : N.charts.total.symm (z₀, 0) = x := by
    rw [← N.center_coordinates, N.charts.total.left_inv N.charts.point]
  have hz : (z₀, (0, 0)) ∈ N.charts.pairDomain := N.section_mem_pairDomain _ N.center
  apply AlgHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have ht := hf (z₀, (0, 0)) hz a b
    change f (z₀, (0, 0)) (a ⊗ₜ[R] b) = _
    simpa only [hc, RelativeTensorPoints.Abelian.RelativeCharts.relativeTensorPoint_tmul] using ht
  | add a b ha hb => simp only [map_add, ha, hb]

/-- An actual algebra-map image of a relative pair varies analytically in
the normalized coordinates, wherever the image belongs to the chart. -/
theorem RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts.pairMap_contDiffOn {s : A →ₐ[ℂ] R}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s)
    (f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A))
    (hf : ∀ t : A ⊗[R] A, ContDiffOn ℂ ω (fun z => f z t) N.charts.pairDomain)
    (m : A →ₐ[ℂ] (A ⊗[R] A)) :
    ContDiffOn ℂ ω (fun z => N.charts.total ((f z).comp m))
      (N.charts.pairDomain ∩ {z | (f z).comp m ∈ N.charts.total.source}) :=
  N.forwardTotal _ (fun z => (f z).comp m) N.charts.pairDomain (fun a => hf (m a))

/-- For an algebra map defined on a principal neighborhood of the relative
fiber product, construct an actual open coordinate neighborhood where its
point map is analytic. The localization and chart domains are obtained
from regular evaluation, rather than assumed analytic neighborhoods. -/
theorem RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts.exists_localized_pairMap {s : A →ₐ[ℂ] R}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s)
    (f : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] A))
    (hf : ∀ t : A ⊗[R] A, ContDiffOn ℂ ω (fun z => f z t) N.charts.pairDomain)
    (z₀ : F × (E × E)) (hz₀ : z₀ ∈ N.charts.pairDomain)
    (g : A ⊗[R] A) (hg : f z₀ g ≠ 0)
    (m : A →ₐ[ℂ] Localization.Away g)
    (hm : (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint (f z₀) g hg).comp m ∈ N.charts.total.source) :
    ∃ (W : Set (F × (E × E)))
      (fg : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)),
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ N.charts.pairDomain ∧
      (∀ z ∈ W, AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g (fg z) = f z) ∧
      (∀ z ∈ W, (fg z).comp m ∈ N.charts.total.source) ∧
      ContDiffOn ℂ ω (fun z => N.charts.total ((fg z).comp m)) W := by
  let V := N.charts.pairDomain ∩ {z | f z g ≠ 0}
  have hV : IsOpen V :=
    (hf g).continuousOn.isOpen_inter_preimage N.charts.pairDomain_isOpen isOpen_ne
  have hzV : z₀ ∈ V := ⟨hz₀, hg⟩
  let p₀ := AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint (f z₀) g hg
  obtain ⟨fg, hfg, hreg⟩ := RelativeTensorPoints.Abelian.RelativeCharts.exists_analytic_localizedFamily g f N.charts.pairDomain hf p₀
  have hfg₀ : fg z₀ = p₀ := by
    apply (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g).injective
    rw [hfg z₀ hzV]
    exact (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp (f z₀) g hg).symm
  let q : F × (E × E) → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A := fun z => (fg z).comp m
  have hq : ContinuousOn q V :=
    RegularRelativeCharts.Abelian.RelativeCharts.continuousOn_affinePoints_of_evaluations q V (fun a => (hreg (m a)).continuousOn)
  let W := V ∩ q ⁻¹' N.charts.total.source
  have hW : IsOpen W := hq.isOpen_inter_preimage hV N.charts.total.open_source
  have hzW : z₀ ∈ W := by
    refine ⟨hzV, ?_⟩
    change (fg z₀).comp m ∈ N.charts.total.source
    rw [hfg₀]
    exact hm
  exact ⟨W, fg, hW, hzW, fun _ hz => hz.1.1,
    fun z hz => hfg z hz.1, fun _ hz => hz.2,
    N.forwardTotal _ q V (fun a => hreg (m a))⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety
