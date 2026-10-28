import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpen
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpenUnion
import OAI.AlgebraicTopology.Duality.Poincare.RationalSingularOpenUnion

/-! # Nested Open Cap Naturality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.NestedOpenCapNaturality

noncomputable section

/-!
# Canonical cap and inclusions between open submanifolds

All support maps below use actual inverse-image compact sets and the literal
inclusion of open subspaces. The canonical integral fundamental classes and
the rational cap pairing are the previously constructed ones.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Subspaces

variable {X : TopCat.{0}} {U V : Opens X}

/-- The compact inverse image of one ambient support maps exactly onto the
compact inverse image in a larger open neighborhood. -/
theorem nestedOpenCompactPreimage_image (h : U ≤ V) (K : U.compactsInside) :
    (Set.inclusion h) '' (CompactOpenIndex.openCompactPreimage U K : Set U) =
      (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) : Set V) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hv
    exact ⟨⟨v.val, K.property hv⟩, hv, rfl⟩

/-- Actual relative cochain restriction between two open neighborhoods of
the same ambient compact support. -/
def nestedOpenPreimageCochainMap (h : U ≤ V) (K : U.compactsInside) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of V)
        (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) : Set V)ᶜ ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V)
    (A := (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ)
    (B := (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) : Set V)ᶜ)
    (fun _ hx => hx)

@[reassoc (attr := simp)]
theorem nestedOpenPreimageCochainMap_inclusion (h : U ≤ V) (K : U.compactsInside) :
    nestedOpenPreimageCochainMap h K ≫
        Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V)
          (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) : Set V)ᶜ ≫
        Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V) :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V) _

/-- The actual ambient restriction factors through the larger open subset. -/
@[reassoc]
theorem compactSupportOpenPreimageCochainRestriction_nested
    (h : U ≤ V) (K : U.compactsInside) :
    CompactSupportOpen.compactSupportOpenPreimageCochainRestriction V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) ≫
        nestedOpenPreimageCochainMap h K =
      CompactSupportOpen.compactSupportOpenPreimageCochainRestriction U K := by
  apply (cancel_mono (CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ)
    (TopCat.of U) (CompactOpenIndex.openCompactPreimage U K))).mp
  rw [Category.assoc, nestedOpenPreimageCochainMap_inclusion,
    ← Category.assoc, CompactSupportOpen.compactSupportOpenPreimageCochainRestriction_inclusion,
    Category.assoc, ← Cohomology.Singular.Functor.singularPullback_comp]
  exact (CompactSupportOpen.compactSupportOpenPreimageCochainRestriction_inclusion U K).symm

/-- The same factorization on the existing relative cohomology groups. -/
@[reassoc]
theorem compactSupportOpenPreimageCohomologyRestriction_nested
    (h : U ≤ V) (K : U.compactsInside) (n : ℕ) :
    CompactSupportOpen.compactSupportOpenPreimageCohomologyRestriction V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) n ≫
        HomologicalComplex.homologyMap (nestedOpenPreimageCochainMap h K) n =
      CompactSupportOpen.compactSupportOpenPreimageCohomologyRestriction U K n := by
  change HomologicalComplex.homologyMap
      (CompactSupportOpen.compactSupportOpenPreimageCochainRestriction V ((CompactSupportInsideMaps.compactsInsideMap h).obj K)) n ≫
    HomologicalComplex.homologyMap (nestedOpenPreimageCochainMap h K) n =
      HomologicalComplex.homologyMap (CompactSupportOpen.compactSupportOpenPreimageCochainRestriction U K) n
  rw [← HomologicalComplex.homologyMap_comp,
    compactSupportOpenPreimageCochainRestriction_nested]

/-- The corresponding actual integral relative homology inclusion. -/
abbrev nestedOpenPreimageHomologyMap (h : U ≤ V) (K : U.compactsInside) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ n ⟶
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of V)
        (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) : Set V)ᶜ n :=
  AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap
    (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V)
    (A := (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ)
    (B := (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) : Set V)ᶜ)
    (fun _ hx => hx) n

end Subspaces

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

private theorem complexCompactFundamentalClass_opensInclusion_of_image
    (U V : Opens M) (h : U ≤ V) (A : Set U) (B : Set V)
    (hA : IsCompact A) (hB : IsCompact B) (himage : (Set.inclusion h) '' A = B)
    (hpair : Set.MapsTo
      (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V) Aᶜ Bᶜ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap
        (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V)
        hpair (2 * d) (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (M := U) A hA) =
      AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (M := V) B hB := by
  subst B
  exact AlgebraicGeometry.CycleClass.Geometric.OpenFundamental.Cycles.complexCompactFundamentalClass_opensInclusion d U V h A hA

/-- The actual canonical classes of the compact inverse images agree under
the nested-open inclusion, including transport to an equal homological degree. -/
theorem complexCompactClassInDegree_nestedOpen (U V : Opens M) (h : U ≤ V)
    (n : ℕ) (hn : n = 2 * d) (K : U.compactsInside) :
    nestedOpenPreimageHomologyMap (X := TopCat.of M) h K n
        (ComplexManifoldCap.complexCompactClassInDegree d (M := U) n hn (CompactOpenIndex.openCompactPreimage U K)) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := V) n hn
        (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap (X := TopCat.of M) h).obj K)) := by
  subst n
  exact complexCompactFundamentalClass_opensInclusion_of_image d U V h
    (CompactOpenIndex.openCompactPreimage U K : Set U)
    (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap (X := TopCat.of M) h).obj K) : Set V)
    (CompactOpenIndex.openCompactPreimage U K).isCompact
    (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap (X := TopCat.of M) h).obj K)).isCompact
    (nestedOpenCompactPreimage_image (X := TopCat.of M) h K) (fun _ hx => hx)

/-- Relative cap for the canonical classes commutes with the actual maps of
the two compact-support pairs inside nested open submanifolds. -/
@[reassoc]
theorem complexCanonicalRelativeCap_nestedOpen (U V : Opens M) (h : U ≤ V)
    (K : U.compactsInside) (p q : ℕ) (hpq : p + q = 2 * d) :
    HomologicalComplex.homologyMap
        (nestedOpenPreimageCochainMap (X := TopCat.of M) h K) p ≫
      SupportCapNaturality.relativeCapWithClass (TopCat.of U) (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ p q
        (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq (CompactOpenIndex.openCompactPreimage U K)) ≫
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
        (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V) q =
    SupportCapNaturality.relativeCapWithClass (TopCat.of V)
      (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap (X := TopCat.of M) h).obj K) : Set V)ᶜ p q
      (ComplexManifoldCap.complexCompactClassInDegree d (M := V) (p + q) hpq
        (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap (X := TopCat.of M) h).obj K))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hc := complexCompactClassInDegree_nestedOpen d U V h (p + q) hpq K
  have hn := SupportCapNaturality.relativeCapHomology_naturality
    (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V)
    (A := (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ)
    (B := (CompactOpenIndex.openCompactPreimage V ((CompactSupportInsideMaps.compactsInsideMap (X := TopCat.of M) h).obj K) : Set V)ᶜ)
    (fun _ hx => hx) p q c
    (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq (CompactOpenIndex.openCompactPreimage U K))
  change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap _ _ (p + q) _ = _ at hc
  rw [hc] at hn
  exact hn

/-- Canonical cap commutes with the actual compact-support extension between
two nested open submanifolds, and the actual ordinary homology inclusion. -/
@[reassoc]
theorem complexManifoldCompactSupportCap_opensInclusion
    (U V : Opens M) (h : U ≤ V) (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportOpen.compactSupportOpenMap (X := TopCat.of M) h p ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq ≫
        Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V) q := by
  apply CompactSupportOpen.compactSupportOpenStageClass_hom_ext (X := TopCat.of M) U p
  intro K
  let KV := (CompactSupportInsideMaps.compactsInsideMap (X := TopCat.of M) h).obj K
  let rV := CompactSupportOpen.compactSupportOpenPreimageCohomologyRestriction (X := TopCat.of M) V KV p
  let rU := CompactSupportOpen.compactSupportOpenPreimageCohomologyRestriction (X := TopCat.of M) U K p
  let rUV := HomologicalComplex.homologyMap
    (nestedOpenPreimageCochainMap (X := TopCat.of M) h K) p
  let cV := SupportCapNaturality.relativeCapWithClass (TopCat.of V) (CompactOpenIndex.openCompactPreimage V KV : Set V)ᶜ p q
    (ComplexManifoldCap.complexCompactClassInDegree d (M := V) (p + q) hpq (CompactOpenIndex.openCompactPreimage V KV))
  let cU := SupportCapNaturality.relativeCapWithClass (TopCat.of U) (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ p q
    (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq (CompactOpenIndex.openCompactPreimage U K))
  let f : TopCat.of U ⟶ TopCat.of V := TopCat.ofHom (ContinuousMap.inclusion h)
  have hsV : CompactSupportOpen.compactSupportOpenStageClass (X := TopCat.of M) V KV p ≫
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq = rV ≫ cV := by
    dsimp only [rV, cV]
    rw [CompactSupportOpen.compactSupportOpenStageClass_preimage, Category.assoc,
      ComplexManifoldCap.complexManifoldCompactSupportCap_stage]
  have hsU : CompactSupportOpen.compactSupportOpenStageClass (X := TopCat.of M) U K p ≫
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq = rU ≫ cU := by
    dsimp only [rU, cU]
    rw [CompactSupportOpen.compactSupportOpenStageClass_preimage, Category.assoc,
      ComplexManifoldCap.complexManifoldCompactSupportCap_stage]
  have hc : rUV ≫ cU ≫ Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f q = cV :=
    complexCanonicalRelativeCap_nestedOpen d U V h K p q hpq
  have hr : rV ≫ rUV = rU :=
    compactSupportOpenPreimageCohomologyRestriction_nested h K p
  calc
    CompactSupportOpen.compactSupportOpenStageClass (X := TopCat.of M) U K p ≫
        (CompactSupportOpen.compactSupportOpenMap (X := TopCat.of M) h p ≫
          ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq) =
      CompactSupportOpen.compactSupportOpenStageClass (X := TopCat.of M) V KV p ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq := by
          rw [← Category.assoc, CompactSupportOpen.compactSupportOpenStageClass_map]
    _ = rV ≫ cV := hsV
    _ = rV ≫ (rUV ≫ cU ≫ Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f q) :=
      congrArg (fun t => rV ≫ t) hc.symm
    _ = rU ≫ cU ≫ Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f q := by
      rw [← Category.assoc, hr]
    _ = CompactSupportOpen.compactSupportOpenStageClass (X := TopCat.of M) U K p ≫
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq ≫
          Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f q) := by
      rw [← Category.assoc, ← Category.assoc, hsU]

/-- The preceding square, evaluated on an actual compact-support class. -/
theorem complexManifoldCompactSupportCap_opensInclusion_apply
    (U V : Opens M) (h : U ≤ V) (p q : ℕ) (hpq : p + q = 2 * d)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) p) :
    ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq
        (CompactSupportOpen.compactSupportOpenMap (X := TopCat.of M) h p c) =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion h) : TopCat.of U ⟶ TopCat.of V) q
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq c) :=
  ConcreteCategory.congr_hom
    (complexManifoldCompactSupportCap_opensInclusion d U V h p q hpq) c

/-- Canonical cap is a natural transformation on all actual open submanifolds. -/
def complexManifoldOpenCapNat (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportOpen.compactSupportOpenCohomologyFunctor (TopCat.of M) p ⟶
      RationalSingularOpenUnion.rationalOpenHomologyFunctor (TopCat.of M) q where
  app U := ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq
  naturality U V f :=
    complexManifoldCompactSupportCap_opensInclusion d U V (leOfHom f) p q hpq

@[simp]
theorem complexManifoldOpenCapNat_app (p q : ℕ) (hpq : p + q = 2 * d) (U : Opens M) :
    (complexManifoldOpenCapNat d (M := M) p q hpq).app U =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq := rfl

/-- The same canonical cap transformation on the exact increasing-open
diagrams used by the proved cohomology and homology colimit comparisons. -/
def complexManifoldIncreasingOpenCapNat (U : ℕ → Opens M) (hU : Monotone U)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportOpenUnion.compactSupportIncreasingOpenDiagram (X := TopCat.of M) U hU p ⟶
      RationalSingularOpenUnion.rationalIncreasingOpenHomologyDiagram (X := TopCat.of M) U hU q :=
  Functor.whiskerLeft hU.functor (complexManifoldOpenCapNat d (M := M) p q hpq)

@[simp]
theorem complexManifoldIncreasingOpenCapNat_app (U : ℕ → Opens M) (hU : Monotone U)
    (p q : ℕ) (hpq : p + q = 2 * d) (i : ℕ) :
    (complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq).app i =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U i) p q hpq := rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.NestedOpenCapNaturality
