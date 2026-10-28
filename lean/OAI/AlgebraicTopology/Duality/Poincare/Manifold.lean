import OAI.AlgebraicTopology.Duality.Poincare.Property
import OAI.AlgebraicTopology.Duality.Poincare.OpenUnion
import OAI.AlgebraicTopology.Duality.Poincare.Empty
import OAI.AlgebraicTopology.Duality.Poincare.MayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.OpenEuclidean
import OAI.AlgebraicTopology.Duality.Poincare.CompactMeaning
import OAI.Topology.Euclidean.FiniteChartCover
import OAI.Topology.Euclidean.CountableBootstrap
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization
import Mathlib.Topology.Bases

/-! # Manifold -/

namespace OAI.AlgebraicTopology.Duality.Poincare.Manifold

noncomputable section

/-!
# Canonical Poincare duality from genuine complex manifold charts

Finite intersections of actual chart domains are homeomorphic to open subsets
of the model space. Finite chart unions, followed by an increasing countable
chart cover, assemble the canonical compact-support cap-product isomorphism.
-/

open Set _root_.TopologicalSpace _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

namespace Globalization

variable (H : Type) [TopologicalSpace H]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The actual open union of finitely many preferred chart domains. -/
def finiteChartUnion (s : Finset M) : Opens M :=
  ⟨⋃ x ∈ s, (chartAt H x).source,
    isOpen_biUnion fun x _ => (chartAt H x).open_source⟩

@[simp]
theorem mem_finiteChartUnion (s : Finset M) (y : M) :
    y ∈ finiteChartUnion H s ↔ ∃ x ∈ s, y ∈ (chartAt H x).source := by
  simp only [finiteChartUnion, Opens.mem_mk, Set.mem_iUnion, exists_prop]

/-- Adding chart centers can only enlarge the corresponding open union. -/
theorem finiteChartUnion_mono : Monotone (finiteChartUnion H (M := M)) := by
  intro s t hst y hy
  obtain ⟨x, hx, hyx⟩ := (mem_finiteChartUnion H s y).mp hy
  exact (mem_finiteChartUnion H t y).mpr ⟨x, hst hx, hyx⟩

/-- Second countability supplies an increasing countable cover by actual
finite unions of preferred chart domains, including the empty-space case. -/
theorem exists_countable_finiteChartCover [SecondCountableTopology M] :
    ∃ c : ℕ → Finset M, Monotone c ∧
      ∀ x : M, ∃ n : ℕ, x ∈ finiteChartUnion H (c n) := by
  classical
  obtain ⟨s, hsc, hcover⟩ :=
    TopologicalSpace.countable_cover_nhds (fun x : M => chart_source_mem_nhds H x)
  let : Countable s := hsc.to_subtype
  let b : s → Set M := fun y => (chartAt H y.val).source
  let c : ℕ → Finset M := fun n =>
    (OAI.Topology.Euclidean.BoxExhaustion.Globalization.CountableFamily.indices b Set.univ n).image Subtype.val
  refine ⟨c, ?_, ?_⟩
  · intro n m hnm
    exact Finset.image_subset_image (OAI.Topology.Euclidean.BoxExhaustion.Globalization.CountableFamily.indices_mono b Set.univ hnm)
  · intro x
    have hx : x ∈ ⋃ y ∈ s, (chartAt H y).source := by
      rw [hcover]
      exact Set.mem_univ x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨n, hn⟩ := OAI.Topology.Euclidean.BoxExhaustion.Globalization.CountableFamily.subset_stage b Set.univ ⟨y, hy⟩ (Set.subset_univ _)
    refine ⟨n, ?_⟩
    have hxn : x ∈ OAI.Topology.Euclidean.BoxExhaustion.Globalization.CountableFamily.stage b Set.univ n := hn hxy
    change x ∈ ⋃ y ∈ (OAI.Topology.Euclidean.BoxExhaustion.Globalization.CountableFamily.indices b Set.univ n).image Subtype.val,
      (chartAt H y).source
    simpa only [OAI.Topology.Euclidean.BoxExhaustion.Globalization.CountableFamily.stage, Finset.set_biUnion_finset_image] using hxn

end Globalization

section

open OAI.AlgebraicTopology.Duality.Poincare.Manifold.Globalization

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The finite-cover induction, specialized to the actual manifold property.
The later local theorem supplies the intersection and binary-gluing inputs. -/
private theorem finiteChartUnion_glue
    (hglue : ∀ U V : Opens M, Property.HasCanonicalPoincareDuality d U →
      Property.HasCanonicalPoincareDuality d V → Property.HasCanonicalPoincareDuality d ↥(U ⊓ V) →
      Property.HasCanonicalPoincareDuality d ↥(U ⊔ V))
    (hintersections : ∀ t : Finset M, t.Nonempty →
      Property.HasCanonicalPoincareDuality d (OAI.Topology.Euclidean.FiniteChartCover.Globalization.chartIntersectionOpen (Fin d → ℂ) t))
    (s : Finset M) : Property.HasCanonicalPoincareDuality d (Globalization.finiteChartUnion (Fin d → ℂ) s) := by
  let P : Set M → Prop := fun S =>
    ∀ hS : IsOpen S, Property.HasCanonicalPoincareDuality d (⟨S, hS⟩ : Opens M)
  have hP : P (⋃ x ∈ s, (chartAt (Fin d → ℂ) x).source) := by
    refine OAI.Topology.Euclidean.CountableBootstrap.Globalization.property_finite_union_of_intersections P ?_ ?_ s
      (fun x : M => (chartAt (Fin d → ℂ) x).source) ?_ ?_
    · intro hS
      let : IsEmpty ↥(⟨∅, hS⟩ : Opens M) := ⟨fun x => x.property⟩
      exact Empty.hasCanonicalPoincareDuality_of_isEmpty d ↥(⟨∅, hS⟩ : Opens M)
    · intro S T hS hT hPS hPT hPST hST
      exact hglue ⟨S, hS⟩ ⟨T, hT⟩ (hPS hS) (hPT hT) (hPST (hS.inter hT))
    · intro x _
      exact (chartAt (Fin d → ℂ) x).open_source
    · intro t _ ht hT
      exact hintersections t ht
  exact hP (Globalization.finiteChartUnion (Fin d → ℂ) s).isOpen

/-- The proved increasing-cover theorem reduces global canonical duality to
actual finite chart unions. The later theorem discharges this local premise. -/
theorem hasCanonicalPoincareDuality_of_finiteChartUnions [SecondCountableTopology M]
    (hfinite : ∀ s : Finset M, Property.HasCanonicalPoincareDuality d (Globalization.finiteChartUnion (Fin d → ℂ) s)) :
    Property.HasCanonicalPoincareDuality d M := by
  obtain ⟨c, hc, hcover⟩ := Globalization.exists_countable_finiteChartCover (Fin d → ℂ) (M := M)
  exact Property.HasCanonicalPoincareDuality.of_increasingOpenCover d
    (fun n => Globalization.finiteChartUnion (Fin d → ℂ) (c n))
    ((Globalization.finiteChartUnion_mono (Fin d → ℂ)).comp hc) hcover (fun n => hfinite (c n))

/-- For compact manifolds, a genuine finite subcover gives the same reduction
without using second countability. -/
theorem compact_hasCanonicalPoincareDuality_of_finiteChartUnions [CompactSpace M]
    (hfinite : ∀ s : Finset M, Property.HasCanonicalPoincareDuality d (Globalization.finiteChartUnion (Fin d → ℂ) s)) :
    Property.HasCanonicalPoincareDuality d M := by
  obtain ⟨s, hs⟩ := OAI.Topology.Euclidean.FiniteChartCover.Globalization.exists_finite_chart_cover (Fin d → ℂ) (M := M)
  apply Property.HasCanonicalPoincareDuality.of_increasingOpenCover d
    (fun _ => Globalization.finiteChartUnion (Fin d → ℂ) s) monotone_const
  · intro x
    refine ⟨0, ?_⟩
    change x ∈ ⋃ y ∈ s, (chartAt (Fin d → ℂ) y).source
    rw [hs]
    exact Set.mem_univ x
  · intro _
    exact hfinite s

end

namespace HasCanonicalPoincareDuality

variable {d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- On a compact manifold, the canonical duality property makes the actual
ordinary cap product with the canonical integral fundamental class invertible. -/
theorem _root_.OAI.AlgebraicTopology.Duality.Poincare.Property.HasCanonicalPoincareDuality.ordinaryCap_isIso (h : Property.HasCanonicalPoincareDuality d M)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    IsIso (CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq) := by
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq) := h.cap_isIso p q hpq
  rw [← CompactMeaning.ordinaryCap_eq_compactSupportCap d p q hpq]
  infer_instance

/-- This is the isomorphism of ordinary groups carried by that actual cap map. -/
def _root_.OAI.AlgebraicTopology.Duality.Poincare.Property.HasCanonicalPoincareDuality.ordinaryDualityIso (h : Property.HasCanonicalPoincareDuality d M)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q := by
  let : IsIso (CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq) := h.ordinaryCap_isIso p q hpq
  exact asIso (CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq)

@[simp]
theorem _root_.OAI.AlgebraicTopology.Duality.Poincare.Property.HasCanonicalPoincareDuality.ordinaryDualityIso_hom (h : Property.HasCanonicalPoincareDuality d M)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (h.ordinaryDualityIso p q hpq).hom = CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq := rfl

/-- The higher-degree vanishing also has its ordinary cohomology meaning on
compact manifolds, through the proved compact-support comparison. -/
theorem _root_.OAI.AlgebraicTopology.Duality.Poincare.Property.HasCanonicalPoincareDuality.ordinaryCohomology_isZero (h : Property.HasCanonicalPoincareDuality d M)
    (p : ℕ) (hp : 2 * d < p) :
    IsZero (Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :=
  (h.cohomology_isZero p hp).of_iso
    (CompactSupportCohomology.compactSupportedCohomologyIso (ModuleCat.of ℚ ℚ) (TopCat.of M) p).symm

end HasCanonicalPoincareDuality

section

open OAI.AlgebraicTopology.Duality.Poincare.Manifold.Globalization

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- Every actual finite chart intersection is an open Euclidean manifold,
and the proved binary Mayer--Vietoris theorem glues their canonical duality. -/
theorem finiteChartUnion_hasCanonicalPoincareDuality (s : Finset M) :
    Property.HasCanonicalPoincareDuality d (Globalization.finiteChartUnion (Fin d → ℂ) s) := by
  apply finiteChartUnion_glue d
    (fun U V hU hV hUV => Property.HasCanonicalPoincareDuality.sup (d := d) U V hU hV hUV)
    (s := s)
  intro t ht
  obtain ⟨x, hx⟩ := ht
  exact OpenEuclidean.openEuclideanChart_hasCanonicalPoincareDuality d
    (OAI.Topology.Euclidean.FiniteChartCover.Globalization.chartIntersectionImageOpen (Fin d → ℂ) t x hx)
    (OAI.Topology.Euclidean.FiniteChartCover.Globalization.chartIntersectionHomeomorph (Fin d → ℂ) t x hx)

/-- Canonical compact-support Poincare duality on every genuine Hausdorff,
second-countable complex manifold. No duality data are attached as hypotheses. -/
theorem complexManifold_hasCanonicalPoincareDuality [SecondCountableTopology M] :
    Property.HasCanonicalPoincareDuality d M :=
  hasCanonicalPoincareDuality_of_finiteChartUnions d
    (finiteChartUnion_hasCanonicalPoincareDuality d)

/-- Compact complex manifolds admit the same canonical duality by their
actual finite chart cover; second countability need not be supplied separately. -/
theorem compactComplexManifold_hasCanonicalPoincareDuality [CompactSpace M] :
    Property.HasCanonicalPoincareDuality d M :=
  compact_hasCanonicalPoincareDuality_of_finiteChartUnions d
    (finiteChartUnion_hasCanonicalPoincareDuality d)

/-- The actual canonical compact-support cap map is the duality isomorphism. -/
def complexManifoldPoincareDuality [SecondCountableTopology M]
    (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q := by
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq) :=
    (complexManifold_hasCanonicalPoincareDuality d (M := M)).cap_isIso p q hpq
  exact asIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq)

@[simp]
theorem complexManifoldPoincareDuality_hom [SecondCountableTopology M]
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (complexManifoldPoincareDuality d (M := M) p q hpq).hom =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq := rfl

/-- For compact manifolds the ordinary duality isomorphism is the actual
singular cap product by the canonical integral fundamental class. -/
def compactComplexManifoldPoincareDuality [CompactSpace M]
    (p q : ℕ) (hpq : p + q = 2 * d) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q :=
  (compactComplexManifold_hasCanonicalPoincareDuality d (M := M)).ordinaryDualityIso p q hpq

@[simp]
theorem compactComplexManifoldPoincareDuality_hom [CompactSpace M]
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (compactComplexManifoldPoincareDuality d (M := M) p q hpq).hom =
      CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq := rfl

/-- Above real dimension, the actual compact-support cohomology vanishes. -/
theorem complexManifold_compactSupportedCohomology_isZero [SecondCountableTopology M]
    (p : ℕ) (hp : 2 * d < p) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :=
  (complexManifold_hasCanonicalPoincareDuality d (M := M)).cohomology_isZero p hp

/-- The same dimensional vanishing holds for ordinary cohomology in the
compact case, through the actual compact-support comparison. -/
theorem compactComplexManifold_singularCohomology_isZero [CompactSpace M]
    (p : ℕ) (hp : 2 * d < p) :
    IsZero (Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :=
  (compactComplexManifold_hasCanonicalPoincareDuality d (M := M)).ordinaryCohomology_isZero p hp

end

namespace IntegralProjectiveVariety

open OAI.AlgebraicTopology.Duality.Poincare.Manifold

/-- The actual analytic realization of an integral smooth projective variety
has canonical Poincare duality, with all manifold hypotheses already proved. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.hasCanonicalPoincareDuality (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Property.HasCanonicalPoincareDuality V.complexDimension V.analyticSpace :=
  compactComplexManifold_hasCanonicalPoincareDuality V.complexDimension (M := V.analyticSpace)

/-- Ordinary rational singular Poincare duality on the variety's actual
complex points, using cap with their canonical integral fundamental class. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.poincareDuality (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (hpq : p + q = 2 * V.complexDimension) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) p ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology q :=
  compactComplexManifoldPoincareDuality V.complexDimension (M := V.analyticSpace) p q hpq

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.poincareDuality_hom (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (hpq : p + q = 2 * V.complexDimension) :
    (V.poincareDuality p q hpq).hom =
      CompactMeaning.complexManifoldOrdinaryCap V.complexDimension (M := V.analyticSpace) p q hpq := rfl

/-- The duality isomorphism is explicitly the ordinary singular cap product. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.poincareDuality_apply (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (hpq : p + q = 2 * V.complexDimension)
    (c : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) p) :
    (V.poincareDuality p q hpq).hom c =
      MixedCapHomology.mixedSingularCapHomology (TopCat.of V.analyticSpace) p q c
        (CompactMeaning.complexFundamentalClassInDegree V.complexDimension (M := V.analyticSpace)
          (p + q) hpq) := rfl

theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.singularCohomology_isZero_above_dimension (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p : ℕ) (hp : 2 * V.complexDimension < p) :
    IsZero (Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) p) :=
  V.hasCanonicalPoincareDuality.ordinaryCohomology_isZero p hp

end IntegralProjectiveVariety

end

end OAI.AlgebraicTopology.Duality.Poincare.Manifold
