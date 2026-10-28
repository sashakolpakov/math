import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyStalk
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactConvexNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteConvexSupport

/-! # Euclidean Compact Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport.Cycles

noncomputable section

/-!
# Compact-support relative homology in Euclidean space

The preliminary lemmas work with actual relative singular chains in a
Hausdorff space. A finite relative cycle extends to an open neighborhood of
its support by avoiding the compact image of its boundary. The proved
local-homology stalk comparison then detects local vanishing on an open
neighborhood. In complex coordinate space, finite compact convex neighborhoods
give vanishing above the real dimension and joint point detection in top degree
for every compact support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0})

/-- The actual homology restrictions compose in the order of support inclusions. -/
theorem relativeComplementHomologyRestriction_trans {U V W : Set X}
    (hUV : U ⊆ V) (hVW : V ⊆ W) (n : ℕ) :
    HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hVW) n ≫
        HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hUV) n =
      HomologicalComplex.homologyMap
        (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X (hUV.trans hVW)) n := by
  rw [← HomologicalComplex.homologyMap_comp, LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_trans]

private theorem supportProjection_d (A : Set X) (i j : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X i) :
    (LocalHomology.Cycles.relativeChainProjection X A).f j ((LocalHomology.Cycles.integralSingularChains X).d i j c) =
      (LocalHomology.Cycles.relativeSingularChains X A).d i j ((LocalHomology.Cycles.relativeChainProjection X A).f i c) :=
  (ConcreteCategory.congr_hom ((LocalHomology.Cycles.relativeChainProjection X A).comm i j) c).symm

variable [T2Space X]

/-- A genuine relative homology class over any support set extends to some
open neighborhood of that support. The open neighborhood is the complement
of the compact geometric image of the boundary of a finite representative. -/
theorem exists_open_relativeHomology_lift (K : Set X) (n : ℕ)
    (a : LocalHomology.Cycles.relativeSingularHomology X Kᶜ n) :
    ∃ (U : Opens X) (hKU : K ⊆ (U : Set X))
      (b : LocalHomology.Cycles.relativeSingularHomology X (U : Set X)ᶜ n),
      HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU) n b = a := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocalHomology.Cycles.relativeSingularChains X Kᶜ) n a
  obtain ⟨c, hc⟩ := LocalHomologyStalk.Cycles.relativeChainProjection_degree_surjective X Kᶜ n
    (z : (LocalHomology.Cycles.relativeSingularChains X Kᶜ).X n)
  let j := (ComplexShape.down ℕ).next n
  let d := (LocalHomology.Cycles.integralSingularChains X).d n j c
  have hdc : (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f j d = 0 := by
    rw [supportProjection_d, hc]
    exact AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero _ n j z
  have hdK : FiniteChainSeparation.Cycles.finiteChainImage X j d ⊆ Kᶜ := by
    intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := (FiniteChainSeparation.Cycles.mem_finiteChainImage_iff X j d x).mp hx
    exact (RelativeChainSupport.Cycles.relativeChainProjection_eq_zero_iff_supported X Kᶜ j d).mp hdc σ hσ hxσ
  let U : Opens X :=
    ⟨(FiniteChainSeparation.Cycles.finiteChainImage X j d)ᶜ, (FiniteChainSeparation.Cycles.finiteChainImage_isClosed X j d).isOpen_compl⟩
  have hKU : K ⊆ (U : Set X) := by
    intro x hxK hxD
    exact hdK hxD hxK
  have hcycle : (LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n := by
    change (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ).d n j
      ((LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c) = 0
    rw [← supportProjection_d]
    apply RelativeChainSupport.Cycles.relativeChainProjection_eq_zero_of_supported
    intro σ hσ x hxσ
    change ¬ x ∉ FiniteChainSeparation.Cycles.finiteChainImage X j d
    exact fun hx => hx ((FiniteChainSeparation.Cycles.mem_finiteChainImage_iff X j d x).mpr ⟨σ, hσ, hxσ⟩)
  let zU : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n := ⟨_, hcycle⟩
  have hmap : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU) n zU = z := by
    apply Subtype.ext
    have hproj := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom
        (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_projection X hKU) n) c
    change (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU).f n
      ((LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c) =
        (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n c at hproj
    exact hproj.trans hc
  refine ⟨U, hKU, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n zU, ?_⟩
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, hmap]

/-- A section with zero local class at a point restricts to zero on an actual
open neighborhood, using the proved injective local-homology stalk map. -/
theorem localHomologyToPoint_eq_zero_neighborhood (U : Opens X) (x : X)
    (hx : x ∈ U) (n : ℕ) (a : LocalHomology.Cycles.relativeSingularHomology X (U : Set X)ᶜ n)
    (ha : LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x hx n a = 0) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hVU) n a = 0 := by
  have hg : (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ U x hx a =
      (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ U x hx 0 := by
    apply LocalHomologyStalk.Cycles.localHomologyStalkToPoint_injective X x n
    calc
      _ = LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x hx n a :=
        ConcreteCategory.congr_hom (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint_germ X x n U hx) a
      _ = 0 := ha
      _ = _ := by simp
  obtain ⟨V, hxV, iVU, iVU', hres⟩ :=
    (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ_eq x hx hx a 0 hg
  refine ⟨V, iVU.le, hxV, ?_⟩
  change HomologicalComplex.homologyMap
      (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X iVU.le) n a = _ at hres
  simpa only [map_zero] using hres

/-- The locus where an open-supported relative class has zero image in local
homology is itself open. This is a consequence of the actual stalk comparison. -/
theorem isOpen_localHomology_zeroLocus (U : Opens X) (n : ℕ)
    (a : LocalHomology.Cycles.relativeSingularHomology X (U : Set X)ᶜ n) :
    IsOpen {x : X | ∃ hx : x ∈ U, LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x hx n a = 0} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxU, hxa⟩
  obtain ⟨V, hVU, hxV, hVa⟩ :=
    localHomologyToPoint_eq_zero_neighborhood X U x hxU n a hxa
  apply Filter.mem_of_superset (V.isOpen.mem_nhds hxV)
  intro y hyV
  refine ⟨hVU hyV, ?_⟩
  have heq := ConcreteCategory.congr_hom
    (ConvexSupportHomology.Cycles.relativeComplementHomologyRestriction_toPoint X hVU y hyV n) a
  change LocalHomologyPresheaf.Cycles.localHomologyToPoint X (V : Set X) y hyV n
      (HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hVU) n a) =
    LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) y (hVU hyV) n a at heq
  rw [hVa, map_zero] at heq
  exact heq.symm

/-- A relative class whose point restrictions vanish on its support extends
to an open neighborhood on which all of its point restrictions still vanish. -/
theorem exists_open_pointwiseZero_relativeHomology_lift (K : Set X) (n : ℕ)
    (a : LocalHomology.Cycles.relativeSingularHomology X Kᶜ n)
    (ha : ∀ (x : X) (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n a = 0) :
    ∃ (U : Opens X) (hKU : K ⊆ (U : Set X))
      (b : LocalHomology.Cycles.relativeSingularHomology X (U : Set X)ᶜ n),
      HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU) n b = a ∧
      ∀ (x : X) (hx : x ∈ U), LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x hx n b = 0 := by
  obtain ⟨U, hKU, b, hba⟩ := exists_open_relativeHomology_lift X K n a
  let W : Opens X :=
    ⟨{x | ∃ hx : x ∈ U, LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x hx n b = 0},
      isOpen_localHomology_zeroLocus X U n b⟩
  have hWU : (W : Set X) ⊆ (U : Set X) := fun _ hx => hx.choose
  have hKW : K ⊆ (W : Set X) := by
    intro x hxK
    refine ⟨hKU hxK, ?_⟩
    have heq := ConcreteCategory.congr_hom
      (ConvexSupportHomology.Cycles.relativeComplementHomologyRestriction_toPoint X hKU x hxK n) b
    change LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hxK n
        (HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU) n b) =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x (hKU hxK) n b at heq
    rw [hba, ha x hxK] at heq
    exact heq.symm
  let bW := HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hWU) n b
  refine ⟨W, hKW, bW, ?_, ?_⟩
  · have heq := ConcreteCategory.congr_hom
      (relativeComplementHomologyRestriction_trans X hKW hWU n) b
    change HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKW) n bW =
      HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU) n b at heq
    exact heq.trans hba
  · intro x hxW
    have heq := ConcreteCategory.congr_hom
      (ConvexSupportHomology.Cycles.relativeComplementHomologyRestriction_toPoint X hWU x hxW n) b
    change LocalHomologyPresheaf.Cycles.localHomologyToPoint X (W : Set X) x hxW n bW =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x (hWU hxW) n b at heq
    exact heq.trans hxW.choose_spec

/-- Vanishing on a cofinal collection of larger supports implies vanishing
on the original support. Cofinality is only required inside open neighborhoods. -/
theorem isZero_relativeHomology_of_cofinal_supports (K : Set X) (n : ℕ)
    (hcofinal : ∀ (U : Opens X), K ⊆ (U : Set X) →
      ∃ (L : Set X) (_hKL : K ⊆ L) (_hLU : L ⊆ (U : Set X)),
        IsZero (LocalHomology.Cycles.relativeSingularHomology X Lᶜ n)) :
    IsZero (LocalHomology.Cycles.relativeSingularHomology X Kᶜ n) := by
  have hzero (a : LocalHomology.Cycles.relativeSingularHomology X Kᶜ n) : a = 0 := by
    obtain ⟨U, hKU, b, hba⟩ := exists_open_relativeHomology_lift X K n a
    obtain ⟨L, hKL, hLU, hL⟩ := hcofinal U hKU
    let : Subsingleton (LocalHomology.Cycles.relativeSingularHomology X Lᶜ n) :=
      ModuleCat.isZero_iff_subsingleton.mp hL
    have hsmall :
        HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hLU) n b = 0 :=
      Subsingleton.elim _ _
    have heq := ConcreteCategory.congr_hom
      (relativeComplementHomologyRestriction_trans X hKL hLU n) b
    change HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKL) n
        (HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hLU) n b) =
      HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU) n b at heq
    rw [hsmall, map_zero, hba] at heq
    exact heq.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- Joint detection by point restrictions passes from a cofinal collection of
larger supports to the original support. The open pointwise-zero lift is what
allows detection on all points of the larger support. -/
theorem relativeHomology_eq_zero_of_cofinal_point_detection (K : Set X) (n : ℕ)
    (hcofinal : ∀ (U : Opens X), K ⊆ (U : Set X) →
      ∃ (L : Set X) (_hKL : K ⊆ L) (_hLU : L ⊆ (U : Set X)),
        ∀ b : LocalHomology.Cycles.relativeSingularHomology X Lᶜ n,
          (∀ (x : X) (hx : x ∈ L), LocalHomologyPresheaf.Cycles.localHomologyToPoint X L x hx n b = 0) → b = 0)
    (a : LocalHomology.Cycles.relativeSingularHomology X Kᶜ n)
    (ha : ∀ (x : X) (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n a = 0) : a = 0 := by
  obtain ⟨U, hKU, b, hba, hb⟩ :=
    exists_open_pointwiseZero_relativeHomology_lift X K n a ha
  obtain ⟨L, hKL, hLU, hL⟩ := hcofinal U hKU
  have hsmall :
      HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hLU) n b = 0 := by
    apply hL
    intro x hxL
    have heq := ConcreteCategory.congr_hom
      (ConvexSupportHomology.Cycles.relativeComplementHomologyRestriction_toPoint X hLU x hxL n) b
    change LocalHomologyPresheaf.Cycles.localHomologyToPoint X L x hxL n
        (HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hLU) n b) =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x (hLU hxL) n b at heq
    exact heq.trans (hb x (hLU hxL))
  have heq := ConcreteCategory.congr_hom
    (relativeComplementHomologyRestriction_trans X hKL hLU n) b
  change HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKL) n
      (HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hLU) n b) =
    HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKU) n b at heq
  rw [hsmall, map_zero, hba] at heq
  exact heq.symm

/-- Relative homology supported on an arbitrary compact subset of complex
coordinate space vanishes above its real dimension. -/
theorem isZero_euclidean_compactSupport (p : ℕ) (K : Set (Fin p → ℂ))
    (hK : IsCompact K) (i : ℕ) (hi : 2 * p < i) :
    IsZero (LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin p → ℂ)) Kᶜ i) := by
  apply isZero_relativeHomology_of_cofinal_supports (TopCat.of (Fin p → ℂ)) K i
  intro U hKU
  obtain ⟨s, radius, hs, hKint, hLU, _⟩ :=
    CompactConvexNeighborhood.Cycles.exists_finite_closedBall_neighborhood hK U.isOpen hKU
  refine ⟨_, hKint.trans interior_subset, hLU, ?_⟩
  exact FiniteConvexSupport.Cycles.finiteConvexSupportHomology_isZero p s
    (fun x => Metric.closedBall x (radius x))
    (fun x hx => (hs x hx).2.2.1)
    (fun x hx => (hs x hx).2.2.2.1) i hi

/-- A top-dimensional class supported on an arbitrary compact subset of
complex coordinate space vanishes when every point restriction vanishes. -/
theorem euclidean_compactSupport_eq_zero_of_pointwise
    (p : ℕ) (K : Set (Fin p → ℂ)) (hK : IsCompact K)
    (a : LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin p → ℂ)) Kᶜ (2 * p))
    (ha : ∀ (x : Fin p → ℂ) (hx : x ∈ K),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x hx (2 * p) a = 0) : a = 0 := by
  refine relativeHomology_eq_zero_of_cofinal_point_detection
    (TopCat.of (Fin p → ℂ)) K (2 * p) ?_ a ha
  intro U hKU
  obtain ⟨s, radius, hs, hKint, hLU, _⟩ :=
    CompactConvexNeighborhood.Cycles.exists_finite_closedBall_neighborhood hK U.isOpen hKU
  refine ⟨_, hKint.trans interior_subset, hLU, ?_⟩
  intro b hb
  exact FiniteConvexSupport.Cycles.finiteConvexSupport_eq_zero p s
    (fun x => Metric.closedBall x (radius x))
    (fun x hx => (hs x hx).2.2.1)
    (fun x hx => (hs x hx).2.2.2.1) b hb

/-- Point restrictions jointly distinguish top-dimensional classes on any
compact support, including an empty support. -/
theorem euclidean_compactSupport_point_ext
    (p : ℕ) (K : Set (Fin p → ℂ)) (hK : IsCompact K)
    {a b : LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin p → ℂ)) Kᶜ (2 * p)}
    (h : ∀ (x : Fin p → ℂ) (hx : x ∈ K),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x hx (2 * p) a =
        LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x hx (2 * p) b) : a = b := by
  apply sub_eq_zero.mp
  apply euclidean_compactSupport_eq_zero_of_pointwise p K hK (a - b)
  intro x hx
  rw [map_sub, h x hx, sub_self]

/-- The product of all actual point-restriction maps is injective in the
top degree for any compact support in complex coordinate space. -/
theorem euclidean_compactSupport_pointRestrictions_injective
    (p : ℕ) (K : Set (Fin p → ℂ)) (hK : IsCompact K) :
    Function.Injective (fun a : LocalHomology.Cycles.relativeSingularHomology
        (TopCat.of (Fin p → ℂ)) Kᶜ (2 * p) =>
      fun x : K => LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x.1 x.2 (2 * p) a) := by
  intro a b hab
  apply euclidean_compactSupport_point_ext p K hK
  intro x hx
  exact congrFun hab ⟨x, hx⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport.Cycles
