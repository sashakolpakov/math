import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental
import OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralGeneratorChange

/-! # Fundamental Normalization -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FundamentalNormalization.Cycles

noncomputable section

/-!
# Compact fundamental classes from a primitive complex model generator

An integral coordinate on the actual top local homology of `ℂ^d` determines
its primitive generator. We transport that generator by actual translations
and complex charts, then choose the unique compact-support class with those
local values. The comparison with the canonical family is proved afterwards.
The only choice parameter is the integral model coordinate, not a family of
manifold orientation classes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A primitive normalization of the actual integral complex model group. -/
abbrev ComplexModelNormalization (d : ℕ) :=
  LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin d → ℂ)) 0 (2 * d) ≃ₗ[ℤ] ℤ

/-- The integral change coefficient from the canonical model generator. -/
def complexModelNormalizationSign (d : ℕ) (e : ComplexModelNormalization d) : ℤ :=
  IntegralGeneratorChange.Cycles.integralGeneratorChange (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) e

theorem complexModelNormalizationSign_isUnit (d : ℕ) (e : ComplexModelNormalization d) :
    IsUnit (complexModelNormalizationSign d e) :=
  IntegralGeneratorChange.Cycles.integralGeneratorChange_isUnit (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) e

theorem complexModelNormalizationSign_eq_one_or_neg_one
    (d : ℕ) (e : ComplexModelNormalization d) :
    complexModelNormalizationSign d e = 1 ∨ complexModelNormalizationSign d e = -1 :=
  IntegralGeneratorChange.Cycles.integralGeneratorChange_eq_one_or_neg_one (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) e

theorem complexModelNormalizationSign_ne_zero (d : ℕ) (e : ComplexModelNormalization d) :
    complexModelNormalizationSign d e ≠ 0 :=
  (complexModelNormalizationSign_isUnit d e).ne_zero

theorem complexModelNormalizationSign_rat_isUnit (d : ℕ) (e : ComplexModelNormalization d) :
    IsUnit (complexModelNormalizationSign d e : ℚ) :=
  (complexModelNormalizationSign_isUnit d e).map (Int.castRingHom ℚ)

theorem complexModelNormalizationSign_rat_ne_zero (d : ℕ) (e : ComplexModelNormalization d) :
    (complexModelNormalizationSign d e : ℚ) ≠ 0 :=
  (complexModelNormalizationSign_rat_isUnit d e).ne_zero

@[simp]
theorem complexModelNormalizationSign_canonical (d : ℕ) :
    complexModelNormalizationSign d (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) = 1 :=
  IntegralGeneratorChange.Cycles.integralGeneratorChange_self _

/-- The chosen model generator transported to a coordinate point by the
actual translation to the origin. -/
def complexCoordinatePointClassWithNormalization (d : ℕ) (e : ComplexModelNormalization d)
    (x : Fin d → ℂ) : LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin d → ℂ)) x (2 * d) :=
  (ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℂ) x (2 * d)).inv (e.symm 1)

@[simp]
theorem complexCoordinatePointClassWithNormalization_to_origin
    (d : ℕ) (e : ComplexModelNormalization d) (x : Fin d → ℂ) :
    (ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℂ) x (2 * d)).hom
        (complexCoordinatePointClassWithNormalization d e x) = e.symm 1 :=
  Iso.inv_hom_id_apply _ _

theorem complexCoordinatePointClassWithNormalization_eq_sign_smul
    (d : ℕ) (e : ComplexModelNormalization d) (x : Fin d → ℂ) :
    complexCoordinatePointClassWithNormalization d e x =
      complexModelNormalizationSign d e • ClosedBall.Cycles.complexCoordinatePointClass d x := by
  change (ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℂ) x (2 * d)).inv (e.symm 1) =
    complexModelNormalizationSign d e •
      (ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℂ) x (2 * d)).inv
        ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d).symm 1)
  rw [IntegralGeneratorChange.Cycles.integralGeneratorChange_generator (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) e,
    map_zsmul]
  rfl

section Local

variable (d : ℕ) (e : ComplexModelNormalization d)
variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℂ) M]

/-- The primitive model generator transported through the actual centered
local chart and its induced local-homology isomorphism. -/
def complexChartLocalClassWithNormalization
    (c : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ c.source) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of M) x (2 * d) :=
  (ComplexChartOrientation.Cycles.complexChartLocalIso c x hx (2 * d)).inv (e.symm 1)

@[simp]
theorem complexChartLocalClassWithNormalization_coordinate
    (c : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ c.source) :
    (ComplexChartOrientation.Cycles.complexChartLocalIso c x hx (2 * d)).hom
        (complexChartLocalClassWithNormalization d e c x hx) = e.symm 1 :=
  Iso.inv_hom_id_apply _ _

theorem complexChartLocalClassWithNormalization_eq_sign_smul
    (c : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ c.source) :
    complexChartLocalClassWithNormalization d e c x hx =
      complexModelNormalizationSign d e • ComplexChartOrientation.Cycles.complexChartLocalClass c x hx := by
  change (ComplexChartOrientation.Cycles.complexChartLocalIso c x hx (2 * d)).inv (e.symm 1) =
    complexModelNormalizationSign d e •
      (ComplexChartOrientation.Cycles.complexChartLocalIso c x hx (2 * d)).inv
        ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d).symm 1)
  rw [IntegralGeneratorChange.Cycles.integralGeneratorChange_generator (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) e,
    map_zsmul]
  rfl

/-- Use the preferred actual chart; independence of the atlas chart follows
from the already proved complex transition theorem. -/
def complexLocalClassWithNormalization (x : M) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of M) x (2 * d) :=
  complexChartLocalClassWithNormalization d e (chartAt (Fin d → ℂ) x) x
    (mem_chart_source (Fin d → ℂ) x)

theorem complexLocalClassWithNormalization_eq_sign_smul (x : M) :
    complexLocalClassWithNormalization d e x =
      complexModelNormalizationSign d e • ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x :=
  complexChartLocalClassWithNormalization_eq_sign_smul d e
    (chartAt (Fin d → ℂ) x) x (mem_chart_source (Fin d → ℂ) x)

theorem complexLocalClassWithNormalization_ne_zero (x : M) :
    complexLocalClassWithNormalization d e x ≠ 0 := by
  intro hz
  have h := complexChartLocalClassWithNormalization_coordinate d e
    (chartAt (Fin d → ℂ) x) x (mem_chart_source (Fin d → ℂ) x)
  change (ComplexChartOrientation.Cycles.complexChartLocalIso (chartAt (Fin d → ℂ) x) x
    (mem_chart_source (Fin d → ℂ) x) (2 * d)).hom
      (complexLocalClassWithNormalization d e x) = e.symm 1 at h
  rw [hz, map_zero] at h
  have hn := congrArg e h
  rw [map_zero, e.apply_symm_apply] at hn
  exact zero_ne_one hn

variable [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- Every complex atlas chart gives the same transported primitive class. -/
theorem complexChartLocalClassWithNormalization_eq_local
    (c : OpenPartialHomeomorph M (Fin d → ℂ)) (hc : c ∈ atlas (Fin d → ℂ) M)
    (x : M) (hx : x ∈ c.source) :
    complexChartLocalClassWithNormalization d e c x hx =
      complexLocalClassWithNormalization d e x := by
  rw [complexChartLocalClassWithNormalization_eq_sign_smul,
    complexLocalClassWithNormalization_eq_sign_smul,
    ComplexChartOrientation.Cycles.complexChartLocalClass_eq_canonical c hc x hx]

theorem complexLocalClassWithNormalization_coordinate
    (c : OpenPartialHomeomorph M (Fin d → ℂ)) (hc : c ∈ atlas (Fin d → ℂ) M)
    (x : M) (hx : x ∈ c.source) :
    (ComplexChartOrientation.Cycles.complexChartLocalIso c x hx (2 * d)).hom
      (complexLocalClassWithNormalization d e x) = e.symm 1 := by
  rw [← complexChartLocalClassWithNormalization_eq_local d e c hc x hx,
    complexChartLocalClassWithNormalization_coordinate]

/-- Without centering, the actual chart takes the local class to the
primitive coordinate class obtained by translation at the image point. -/
theorem complexLocalClassWithNormalization_chart [T1Space M]
    (c : OpenPartialHomeomorph M (Fin d → ℂ)) (hc : c ∈ atlas (Fin d → ℂ) M)
    (x : M) (hx : x ∈ c.source) :
    (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
      (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) c x hx (2 * d)).hom
        (complexLocalClassWithNormalization d e x) =
      complexCoordinatePointClassWithNormalization d e (c x) := by
  rw [complexLocalClassWithNormalization_eq_sign_smul, map_zsmul,
    ComplexCoordinateComparison.Cycles.complexCanonicalLocalClass_chart c hc x hx,
    complexCoordinatePointClassWithNormalization_eq_sign_smul]

end Local

variable (d : ℕ) (e : ComplexModelNormalization d)
variable {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The genuinely transported local values admit a compact-support class.
The scalar comparison proves existence, not the definition of the family. -/
theorem exists_complexCompactFundamentalClassWithNormalization
    (K : Set M) (hK : IsCompact K) :
    ∃ a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d),
      ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * d) a =
        complexLocalClassWithNormalization d e x := by
  refine ⟨complexModelNormalizationSign d e • ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK, ?_⟩
  intro x hx
  rw [map_zsmul, ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint,
    complexLocalClassWithNormalization_eq_sign_smul]

/-- The actual compact fundamental class specified by the primitive model
generator and its transported point-local values. -/
def complexCompactFundamentalClassWithNormalization (K : Set M) (hK : IsCompact K) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d) :=
  (exists_complexCompactFundamentalClassWithNormalization d e K hK).choose

theorem complexCompactFundamentalClassWithNormalization_atPoint
    (K : Set M) (hK : IsCompact K) (x : M) (hx : x ∈ K) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * d)
        (complexCompactFundamentalClassWithNormalization d e K hK) =
      complexLocalClassWithNormalization d e x :=
  (exists_complexCompactFundamentalClassWithNormalization d e K hK).choose_spec x hx

/-- Uniqueness uses actual top-dimensional pointwise restriction. -/
theorem complexCompactFundamentalClassWithNormalization_unique
    (K : Set M) (hK : IsCompact K)
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d))
    (ha : ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * d) a =
      complexLocalClassWithNormalization d e x) :
    a = complexCompactFundamentalClassWithNormalization d e K hK := by
  apply ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext d K hK
  intro x hx
  exact (ha x hx).trans
    (complexCompactFundamentalClassWithNormalization_atPoint d e K hK x hx).symm

theorem existsUnique_complexCompactFundamentalClassWithNormalization
    (K : Set M) (hK : IsCompact K) :
    ∃! a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d),
      ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * d) a =
        complexLocalClassWithNormalization d e x :=
  ⟨complexCompactFundamentalClassWithNormalization d e K hK,
    complexCompactFundamentalClassWithNormalization_atPoint d e K hK,
    complexCompactFundamentalClassWithNormalization_unique d e K hK⟩

/-- The newly constructed family differs from the canonical family by the
single integral sign determined by the model normalization. -/
theorem complexCompactFundamentalClassWithNormalization_eq_sign_smul
    (K : Set M) (hK : IsCompact K) :
    complexCompactFundamentalClassWithNormalization d e K hK =
      complexModelNormalizationSign d e • ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK := by
  apply ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext d K hK
  intro x hx
  rw [complexCompactFundamentalClassWithNormalization_atPoint, map_zsmul,
    ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint, complexLocalClassWithNormalization_eq_sign_smul]

theorem complexCompactFundamentalClassWithNormalization_restriction
    (K L : Set M) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M) hKL (2 * d)
        (complexCompactFundamentalClassWithNormalization d e L hL) =
      complexCompactFundamentalClassWithNormalization d e K hK := by
  apply complexCompactFundamentalClassWithNormalization_unique d e K hK
  intro x hx
  rw [FiniteSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint_apply,
    complexCompactFundamentalClassWithNormalization_atPoint]

theorem complexCompactFundamentalClassWithNormalization_ne_zero
    (K : Set M) (hK : IsCompact K) (hne : K.Nonempty) :
    complexCompactFundamentalClassWithNormalization d e K hK ≠ 0 := by
  intro hz
  obtain ⟨x, hx⟩ := hne
  have h := complexCompactFundamentalClassWithNormalization_atPoint d e K hK x hx
  rw [hz, map_zero] at h
  exact complexLocalClassWithNormalization_ne_zero d e x h.symm

theorem complexCompactFundamentalClassWithNormalization_empty :
    complexCompactFundamentalClassWithNormalization d e (∅ : Set M) isCompact_empty = 0 := by
  rw [complexCompactFundamentalClassWithNormalization_eq_sign_smul,
    ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_empty, zsmul_zero]

@[simp]
theorem complexCompactFundamentalClassWithNormalization_canonical
    (K : Set M) (hK : IsCompact K) :
    complexCompactFundamentalClassWithNormalization d
        (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) K hK =
      ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK := by
  rw [complexCompactFundamentalClassWithNormalization_eq_sign_smul,
    complexModelNormalizationSign_canonical, one_zsmul]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FundamentalNormalization.Cycles
