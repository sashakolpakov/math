import OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCap
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly
import OAI.AlgebraicTopology.Products.CapCompatibility

/-! # Support Cap Naturality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportCapNaturality

noncomputable section

/-!
# Naturality of the cap product with support

The rational relative cochains are the actual kernels of restriction and
the integral relative chains are the actual quotients by subspace chains.
Their finite cap pairing commutes with every continuous map of pairs.
Consequently, enlarging a compact support in the cochain argument has exactly
the same effect as restricting the relative chain argument to that support.

The excision identities below use the proved inclusion-of-pairs comparison.
They apply to arbitrary represented classes, without an orientation or
duality hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles OAI.AlgebraicTopology.Products.CapCompatibility

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem relativeCochainMap_inclusion_apply
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (p : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B).X p) :
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h).f p c) =
      (Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f p
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y B).f p c) :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) f h) p) c

private theorem relativeChainMap_projection_apply
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h).f n ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n z) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection Y B).f n ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f n z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality f h) n) z

private theorem scalarChainMap_id (X : TopCat.{0}) :
    Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (𝟙 X) = 𝟙 (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) := by
  change (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map (𝟙 X)) = _
  exact CategoryTheory.Functor.map_id _ X

private theorem scalarHomologyPushforward_id (X : TopCat.{0}) (q : ℕ) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (𝟙 X) q =
      𝟙 ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q) := by
  change HomologicalComplex.homologyMap (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (𝟙 X)) q = _
  rw [scalarChainMap_id, HomologicalComplex.homologyMap_id]

/-- Naturality of the actual relative finite cap product for every map of pairs. -/
theorem relativeCap_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f q
        (SupportRelativeCap.relativeCap X A p q
          ((Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h).f p c) z) =
      SupportRelativeCap.relativeCap Y B p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h).f (p + q) z) := by
  obtain ⟨z, rfl⟩ := SupportRelativeCap.relativeChainProjection_surjective X A (p + q) z
  rw [SupportRelativeCap.relativeCap_projection, relativeChainMap_projection_apply,
    SupportRelativeCap.relativeCap_projection, relativeCochainMap_inclusion_apply]
  exact IntegralCapCoefficients.mixedSingularCap_naturality f p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y B).f p c) z

/-- The same naturality identity on actual relative cocycles and cycles. -/
theorem relativeCapCycles_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f) q
        (SupportRelativeCap.relativeCapCycles X A p q
          (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) p c) z) =
      SupportRelativeCap.relativeCapCycles Y B p q c
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h) (p + q) z) := by
  apply Subtype.ext
  exact relativeCap_naturality f h p q c.val z.val

/-- Naturality descends to the existing categorical relative (co)homology groups. -/
theorem relativeCapHomology_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q)) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f q
        (SupportRelativeCap.relativeCapHomology X A p q
          (Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h p c) z) =
      SupportRelativeCap.relativeCapHomology Y B p q c
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f h (p + q) z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) p c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z
  change (HomologicalComplex.homologyMap (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f) q)
      (SupportRelativeCap.relativeCapHomology X A p q
        ((HomologicalComplex.homologyMap
          (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) p)
            (Cohomology.Singular.Representatives.cochainClass _ p c)) (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) z)) =
    SupportRelativeCap.relativeCapHomology Y B p q (Cohomology.Singular.Representatives.cochainClass _ p c)
      ((HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h) (p + q))
        (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) z))
  rw [Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, SupportRelativeCap.relativeCapHomology_class_class,
    Cohomology.Singular.EvaluationNaturality.chainClass_naturality, Cohomology.Singular.EvaluationNaturality.chainClass_naturality, SupportRelativeCap.relativeCapHomology_class_class]
  exact congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y) q)
    (relativeCapCycles_naturality f h p q c z)

/-- Enlarging the cochain support equals restricting the relative chain support. -/
theorem relativeCap_support_enlargement
    {X : TopCat.{0}} {K L : Compacts X} (h : K ≤ L) (p q : ℕ)
    (c : (CompactSupportCohomology.compactSupportCochainStage (ModuleCat.of ℚ ℚ) X K).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (L : Set X)ᶜ).X (p + q)) :
    SupportRelativeCap.relativeCap X (L : Set X)ᶜ p q
        ((CompactSupportCohomology.compactSupportCochainMap (ModuleCat.of ℚ ℚ) h).f p c) z =
      SupportRelativeCap.relativeCap X (K : Set X)ᶜ p q c
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X h).f (p + q) z) := by
  have hn := relativeCap_naturality (𝟙 X)
    (A := (L : Set X)ᶜ) (B := (K : Set X)ᶜ)
    (fun _ hx hxK => hx (h hxK)) p q c z
  rw [scalarChainMap_id] at hn
  exact hn

/-- The actual support transition maps satisfy cap naturality on (co)homology. -/
theorem relativeCapHomology_support_enlargement
    {X : TopCat.{0}} {K L : Compacts X} (h : K ≤ L) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (L : Set X)ᶜ (p + q)) :
    SupportRelativeCap.relativeCapHomology X (L : Set X)ᶜ p q
        (CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h p c) z =
      SupportRelativeCap.relativeCapHomology X (K : Set X)ᶜ p q c
        (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) z) := by
  have hn := relativeCapHomology_naturality (𝟙 X)
    (A := (L : Set X)ᶜ) (B := (K : Set X)ᶜ)
    (fun _ hx hxK => hx (h hxK)) p q c z
  rw [scalarHomologyPushforward_id] at hn
  exact hn

/-- A fixed actual relative homology class gives a rational-linear cap map. -/
def relativeCapWithClass (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q)) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p ⟶
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q :=
  ModuleCat.ofHom {
    toFun := fun c => SupportRelativeCap.relativeCapHomology X A p q c z
    map_add' c d := by
      simp only [map_add, LinearMap.add_apply]
    map_smul' r c := by
      simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }

@[simp]
theorem relativeCapWithClass_apply (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q))
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p) :
    relativeCapWithClass X A p q z c = SupportRelativeCap.relativeCapHomology X A p q c z := rfl

/-- The cap maps from compact support stages form the required commutative
square with the actual cohomology and relative homology transition maps. -/
@[reassoc]
theorem relativeCapWithClass_support_enlargement
    {X : TopCat.{0}} {K L : Compacts X} (h : K ≤ L) (p q : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (L : Set X)ᶜ (p + q)) :
    CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h p ≫
        relativeCapWithClass X (L : Set X)ᶜ p q z =
      relativeCapWithClass X (K : Set X)ᶜ p q
        (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) z) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact relativeCapHomology_support_enlargement h p q c z

/-- A compatible family of actual integral support-relative homology classes
acts on the genuine compact-support cohomology colimit. This is a construction
on supplied homology classes; it does not assume or assert their geometric
existence as orientation classes. -/
def compactSupportedCapOfCompatibleClasses (X : TopCat.{0}) (p q : ℕ)
    (z : ∀ K : Compacts X, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (K : Set X)ᶜ (p + q))
    (hz : ∀ (K L : Compacts X) (h : K ≤ L),
      AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) (z L) = z K) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p ⟶
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q :=
  CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) X p
    (fun K => relativeCapWithClass X (K : Set X)ᶜ p q (z K))
    (fun K L h => by rw [relativeCapWithClass_support_enlargement, hz K L h])

/-- Evaluation of the descended map on a compact-support stage is exactly
the actual relative cap with that stage's homology class. -/
@[reassoc (attr := simp)]
theorem compactSupportedCapOfCompatibleClasses_stage (X : TopCat.{0}) (p q : ℕ)
    (z : ∀ K : Compacts X, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (K : Set X)ᶜ (p + q))
    (hz : ∀ (K L : Compacts X) (h : K ≤ L),
      AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) (z L) = z K)
    (K : Compacts X) :
    CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K p ≫
        compactSupportedCapOfCompatibleClasses X p q z hz =
      relativeCapWithClass X (K : Set X)ᶜ p q (z K) :=
  CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) X p _ _ K

/-- The stage formula characterizes the descended map uniquely. -/
theorem compactSupportedCapOfCompatibleClasses_unique (X : TopCat.{0}) (p q : ℕ)
    (z : ∀ K : Compacts X, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (K : Set X)ᶜ (p + q))
    (hz : ∀ (K L : Compacts X) (h : K ≤ L),
      AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) (z L) = z K)
    (F : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p ⟶
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q)
    (hF : ∀ K : Compacts X,
      CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K p ≫ F =
        relativeCapWithClass X (K : Set X)ᶜ p q (z K)) :
    F = compactSupportedCapOfCompatibleClasses X p q z hz := by
  apply CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) X p
  intro K
  rw [hF K, compactSupportedCapOfCompatibleClasses_stage]

/-- Cap naturality for the actual inclusion of a support neighborhood. -/
theorem relativeCapHomology_excision (X : TopCat.{0}) (U K : Set X) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) (p + q)) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) q
        (SupportRelativeCap.relativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) p q
          ((HomologicalComplex.homologyMap (CompactSupportExcision.compactSupportExcisionCochainMap X U K) p) c) z) =
      SupportRelativeCap.relativeCapHomology X Kᶜ p q c
        ((HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionChainMap X U K) (p + q)) z) :=
  relativeCapHomology_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ hx => hx) p q c z

/-- Computing a relative cap inside a compact support's open neighborhood
and pushing it forward gives the original ordinary homology class. -/
theorem relativeCapHomology_excision_inv (X : TopCat.{0}) [T2Space X]
    (U K : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X Kᶜ (p + q)) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) q
        (SupportRelativeCap.relativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) p q
          ((HomologicalComplex.homologyMap (CompactSupportExcision.compactSupportExcisionCochainMap X U K) p) c)
          ((AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU (p + q)).inv z)) =
      SupportRelativeCap.relativeCapHomology X Kᶜ p q c z := by
  let e := AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU (p + q)
  have hn := relativeCapHomology_excision X U K p q c (e.inv z)
  change _ = SupportRelativeCap.relativeCapHomology X Kᶜ p q c (e.hom (e.inv z)) at hn
  rw [show e.hom (e.inv z) = z from e.toLinearEquiv.apply_symm_apply z] at hn
  exact hn

/-- The actual inclusion of complementary pairs for a compact support in
an open subspace, on integral relative homology. -/
abbrev compactSupportOpenHomologyMap {X : TopCat.{0}}
    (U : Opens X) (K : Compacts U) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) (K : Set U)ᶜ n ⟶
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (CompactSupportExcision.openSupportImage U K : Set X)ᶜ n :=
  AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap U.inclusion'
    (A := (K : Set U)ᶜ) (B := (CompactSupportExcision.openSupportImage U K : Set X)ᶜ)
    (by
      rintro x hx ⟨y, hy, hxy⟩
      exact hx ((Subtype.ext hxy) ▸ hy)) n

/-- Cap naturality for the compact image of a support in an actual open subspace. -/
theorem compactSupportOpenStageCap_naturality {X : TopCat.{0}}
    (U : Opens X) (K : Compacts U) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X
      (CompactSupportExcision.openSupportImage U K : Set X)ᶜ p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) (K : Set U)ᶜ (p + q)) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) U.inclusion' q
        (SupportRelativeCap.relativeCapHomology (TopCat.of U) (K : Set U)ᶜ p q
          ((HomologicalComplex.homologyMap (CompactSupportExcision.compactSupportOpenStageRestriction U K) p) c) z) =
      SupportRelativeCap.relativeCapHomology X (CompactSupportExcision.openSupportImage U K : Set X)ᶜ p q c
        (compactSupportOpenHomologyMap U K (p + q) z) :=
  relativeCapHomology_naturality U.inclusion' _ p q c z

/-- Extending a supported cohomology class from an open subspace and
including its relative homology argument agrees with ordinary pushforward
of their cap product. The extension is the inverse of proved excision. -/
theorem compactSupportOpenStageCap_extension {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (K : Set U)ᶜ p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) (K : Set U)ᶜ (p + q)) :
    SupportRelativeCap.relativeCapHomology X (CompactSupportExcision.openSupportImage U K : Set X)ᶜ p q
        ((CompactSupportExcision.compactSupportOpenStageIso U K p).inv c)
        (compactSupportOpenHomologyMap U K (p + q) z) =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) U.inclusion' q
        (SupportRelativeCap.relativeCapHomology (TopCat.of U) (K : Set U)ᶜ p q c z) := by
  let e := CompactSupportExcision.compactSupportOpenStageIso U K p
  have hn := compactSupportOpenStageCap_naturality U K p q (e.inv c) z
  change Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) U.inclusion' q
      (SupportRelativeCap.relativeCapHomology (TopCat.of U) (K : Set U)ᶜ p q (e.hom (e.inv c)) z) = _ at hn
  rw [show e.hom (e.inv c) = c from e.toLinearEquiv.apply_symm_apply c] at hn
  exact hn.symm

/-- The open-excision compatibility as a square of rational-linear maps. -/
@[reassoc]
theorem relativeCapWithClass_openExtension {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (p q : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) (K : Set U)ᶜ (p + q)) :
    (CompactSupportExcision.compactSupportOpenStageIso U K p).inv ≫
        relativeCapWithClass X (CompactSupportExcision.openSupportImage U K : Set X)ᶜ p q
          (compactSupportOpenHomologyMap U K (p + q) z) =
      relativeCapWithClass (TopCat.of U) (K : Set U)ᶜ p q z ≫
        Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) U.inclusion' q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact compactSupportOpenStageCap_extension U K p q c z

/-- The cap maps of compatible actual support classes commute with the
proved extension map on compact-support cohomology whenever the classes
themselves commute with the actual open inclusion. -/
theorem compactSupportedCapOfCompatibleClasses_open
    {X : TopCat.{0}} [T2Space X] (U : Opens X) (p q : ℕ)
    (zX : ∀ K : Compacts X, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (K : Set X)ᶜ (p + q))
    (hzX : ∀ (K L : Compacts X) (h : K ≤ L),
      AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) (zX L) = zX K)
    (zU : ∀ K : Compacts U,
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) (K : Set U)ᶜ (p + q))
    (hzU : ∀ (K L : Compacts U) (h : K ≤ L),
      AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of U) h (p + q) (zU L) = zU K)
    (hopen : ∀ K : Compacts U,
      compactSupportOpenHomologyMap U K (p + q) (zU K) = zX (CompactSupportExcision.openSupportImage U K)) :
    CompactSupportExcision.compactSupportOpenExtension U p ≫ compactSupportedCapOfCompatibleClasses X p q zX hzX =
      compactSupportedCapOfCompatibleClasses (TopCat.of U) p q zU hzU ≫
        Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) U.inclusion' q := by
  apply CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of U) p
  intro K
  calc
    CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K p ≫
        (CompactSupportExcision.compactSupportOpenExtension U p ≫ compactSupportedCapOfCompatibleClasses X p q zX hzX) =
      (CompactSupportExcision.compactSupportOpenStageIso U K p).inv ≫
        relativeCapWithClass X (CompactSupportExcision.openSupportImage U K : Set X)ᶜ p q
          (zX (CompactSupportExcision.openSupportImage U K)) := by
      rw [← Category.assoc, CompactSupportExcision.compactSupportCohomologyι_openExtension, Category.assoc,
        compactSupportedCapOfCompatibleClasses_stage]
    _ = relativeCapWithClass (TopCat.of U) (K : Set U)ᶜ p q (zU K) ≫
        Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) U.inclusion' q := by
      rw [← hopen K, relativeCapWithClass_openExtension]
    _ = CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K p ≫
        (compactSupportedCapOfCompatibleClasses (TopCat.of U) p q zU hzU ≫
          Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) U.inclusion' q) := by
      rw [← Category.assoc, compactSupportedCapOfCompatibleClasses_stage]

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportCapNaturality
