import OAI.AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedSheafFlasque
import OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalAtlas
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSupportGerm

/-! # Global Support Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity

noncomputable section

/-!
# From actual local support cohomology to global support cohomology

The initial statements turn vanishing of the actual stalk cohomology of a
flasque rational sheaf complex into vanishing of its global section
cohomology. They use mathlib's stalk detection of sheaf exactness and the
proved flasque low-degree theorem. Local vanishing remains an explicit input
in these general statements; it is not a definition of geometric purity.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree
open scoped _root_.Manifold ContDiff

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

universe u

/-- Exactness of a rational sheaf complex is detected on its genuine stalk
complexes. -/
theorem rationalSheafComplex_exactAt_iff_stalk {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) (n : ℕ) :
    K.ExactAt n ↔ ∀ x : X, (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K x).ExactAt n :=
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (K.sc n)

/-- Vanishing of actual stalk cohomology implies exactness of the sheaf
complex in that degree. -/
theorem rationalSheafComplex_exactAt_of_stalk_isZero {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) (n : ℕ)
    (hs : ∀ x : X, IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K x).homology n)) :
    K.ExactAt n := by
  apply (rationalSheafComplex_exactAt_iff_stalk K n).2
  intro x
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hs x)

/-- The genuine cohomology sheaf vanishes when its stalk cohomology does. -/
theorem rationalSheafComplex_homology_isZero_of_stalk {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) (n : ℕ)
    (hs : ∀ x : X, IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K x).homology n)) :
    IsZero (K.homology n) :=
  (rationalSheafComplex_exactAt_of_stalk_isZero K n hs).isZero_homology

/-- Low-degree stalk vanishing for a termwise flasque rational sheaf complex
implies exactness of its actual global-section complex. -/
theorem rationalFlasqueGlobal_exactAt_of_stalk {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (d : ℕ)
    (hs : ∀ (x : X) (n : ℕ), n < d →
      IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K x).homology n))
    (n : ℕ) (hn : n < d) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex (⊤ : Opens X) K).ExactAt n :=
  AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegree_exactAt K hK d
    (fun q hq => rationalSheafComplex_exactAt_of_stalk_isZero K q (fun x => hs x q hq))
    n hn

/-- Global cohomology vanishes in the same lower range. -/
theorem rationalFlasqueGlobal_homology_isZero_of_stalk {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (d : ℕ)
    (hs : ∀ (x : X) (n : ℕ), n < d →
      IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K x).homology n))
    (n : ℕ) (hn : n < d) :
    IsZero ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex (⊤ : Opens X) K).homology n) :=
  (rationalFlasqueGlobal_exactAt_of_stalk K hK d hs n hn).isZero_homology

/-- At the first possible nonzero degree, the canonical edge isomorphism
uses the local vanishing theorem through actual stalk complexes. -/
def rationalFlasqueFirstCohomologyIso_of_stalk {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (d : ℕ)
    (hs : ∀ (x : X) (n : ℕ), n < d →
      IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K x).homology n)) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex (⊤ : Opens X) K).homology d ≅
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections (⊤ : Opens X)).obj (K.homology d) :=
  AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueFirstCohomologyIso K hK d
    (fun q hq => rationalSheafComplex_exactAt_of_stalk_isZero K q (fun x => hs x q hq))

section SupportedComplex

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- The actual supported complex of a termwise flasque module sheaf complex
is termwise flasque. This uses the special closed-support kernel theorem. -/
theorem supportedSheafComplex_isFlasque (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((SupportStalkVanishes.Cohomology.supportedSheafComplex O K).X n) := by
  have := hK n
  have : TopCat.Presheaf.IsFlasque
      ((TopCat.Sheaf.forget (ModuleCat.{0} R) X).obj (SheafClosedSupport.Cohomology.closedSupportSheaf O (K.X n))) := by
    change TopCat.Sheaf.IsFlasque (SheafClosedSupport.Cohomology.closedSupportSheaf O (K.X n))
    infer_instance
  let e := (TopCat.Sheaf.forget (ModuleCat.{0} R) X).mapIso
    (SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K n).symm
  apply AlgebraicTopology.Cohomology.Singular.CochainFlasque.presheaf_isFlasque_of_pointwise_epi e.hom
  intro U
  have := (e.app U).isIso_hom
  infer_instance

/-- On a metrizable space, every degree of the genuine singular cochain
sheaf with support in the closed complement of `O` is flasque. -/
theorem supportedSingularSheaf_isFlasque_of_metrizable
    (M : ModuleCat.{0} R) (X : TopCat.{0}) [MetrizableSpace X]
    (O : Opens X) (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).X n) :=
  supportedSheafComplex_isFlasque O
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X))
    (AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable M X) n

end SupportedComplex

/-- Low-degree vanishing of the actual supported stalks implies low-degree
vanishing of the actual global supported-section cohomology. -/
theorem supportedSingularGlobal_homology_isZero_of_stalk
    (X : TopCat.{0}) [MetrizableSpace X] (O : Opens X) (d : ℕ)
    (hs : ∀ (x : X) (n : ℕ), n < d → IsZero
      ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
        (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) x).homology n))
    (n : ℕ) (hn : n < d) :
    IsZero ((SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) X O ⊤).homology n) :=
  rationalFlasqueGlobal_homology_isZero_of_stalk
    (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O)
    (supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X O)
    d hs n hn

/-- The first global supported-section cohomology is canonically the
sections of the genuine supported cohomology sheaf, using actual stalk
vanishing as the local input. -/
def supportedSheafGlobalFirstCohomologyIso_of_stalk
    (X : TopCat.{0}) [MetrizableSpace X] (O : Opens X) (d : ℕ)
    (hs : ∀ (x : X) (n : ℕ), n < d → IsZero
      ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
        (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) x).homology n)) :
    (SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) X O ⊤).homology d ≅
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.obj (op ⊤) :=
  rationalFlasqueFirstCohomologyIso_of_stalk
    (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O)
    (supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X O)
    d hs

/-- The genuine global relative cochain comparison gives this canonical
isomorphism on rational cohomology. -/
def relativeSupportedGlobalCohomologyIso (X : TopCat.{0}) [MetrizableSpace X]
    (O : Opens X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) n ≅
      (SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) X O ⊤).homology n := by
  letI := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable ℚ X O
  exact isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O) n

/-- This isomorphism's map is exactly the map induced by the actual
relative-to-supported cochain comparison. -/
@[simp]
theorem relativeSupportedGlobalCohomologyIso_hom (X : TopCat.{0}) [MetrizableSpace X]
    (O : Opens X) (n : ℕ) :
    (relativeSupportedGlobalCohomologyIso X O n).hom =
      HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O) n := rfl

/-- Actual relative singular cohomology vanishes below the range in which
the supported singular stalk cohomology vanishes. -/
theorem supportCohomology_isZero_of_stalk (X : TopCat.{0}) [MetrizableSpace X]
    (O : Opens X) (d : ℕ)
    (hs : ∀ (x : X) (n : ℕ), n < d → IsZero
      ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
        (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) x).homology n))
    (n : ℕ) (hn : n < d) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) n) :=
  (supportedSingularGlobal_homology_isZero_of_stalk X O d hs n hn).of_iso
    (relativeSupportedGlobalCohomologyIso X O n)

/-- The relative first-degree edge map is the composition of the actual
relative cochain comparison with the canonical flasque edge isomorphism. -/
def supportedGlobalFirstCohomologyIso_of_stalk (X : TopCat.{0}) [MetrizableSpace X]
    (O : Opens X) (d : ℕ)
    (hs : ∀ (x : X) (n : ℕ), n < d → IsZero
      ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
        (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) x).homology n)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d ≅
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.obj (op ⊤) :=
  relativeSupportedGlobalCohomologyIso X O d ≪≫
    supportedSheafGlobalFirstCohomologyIso_of_stalk X O d hs

/-- To apply the global theorem it suffices to check local vanishing on
the support; outside it the actual supported stalk complex is already zero. -/
theorem supportCohomology_isZero_of_stalk_on_support
    (X : TopCat.{0}) [MetrizableSpace X] (O : Opens X) (d : ℕ)
    (hs : ∀ (x : X), x ∉ O → ∀ (n : ℕ), n < d → IsZero
      ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
        (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) x).homology n))
    (n : ℕ) (hn : n < d) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) n) := by
  apply supportCohomology_isZero_of_stalk X O d _ n hn
  intro x q hq
  by_cases hx : x ∈ O
  · exact SupportStalkVanishes.Cycles.supportedSingularSheaf_stalk_homology_isZero_of_mem (ModuleCat.of ℚ ℚ) O x hx q
  · exact hs x hx q hq

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]
  [MetrizableSpace N]

/-- Actual supported stalk cohomology vanishes below twice the complex
codimension of a closed analytic immersion. The normal pair is constructed
from the injective derivative and the inverse function theorem. -/
theorem closedComplexImmersion_supportedStalk_homology_isZero
    (f : M → N) (hf : Topology.IsClosedEmbedding f)
    (hsmooth : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (y : N) (n : ℕ) (hn : n < 2 * (Module.finrank ℂ F - Module.finrank ℂ E)) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f hf)) y).homology n) := by
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    let P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E
        (Fin (ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) → ℂ) f x :=
      ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hsmooth hdf hf x
    have hnormal : n < 2 * Module.finrank ℂ (Fin (ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) → ℂ) := by
      simpa only [Module.finrank_fin_fun, ComplexNormalAtlas.Cycles.complexImmersionCodimension] using hn
    exact P.supportedStalk_homology_isZero_of_lt
      (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f hf) rfl n hnormal
  · exact SupportStalkVanishes.Cycles.supportedSingularSheaf_stalk_homology_isZero_of_mem (X := TopCat.of N)
      (ModuleCat.of ℚ ℚ) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f hf) y hy n

/-- The genuine supported singular sheaf complex is exact below the real
codimension of a closed analytic immersion. -/
theorem closedComplexImmersion_supportedSheaf_exactAt
    (f : M → N) (hf : Topology.IsClosedEmbedding f)
    (hsmooth : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (n : ℕ) (hn : n < 2 * (Module.finrank ℂ F - Module.finrank ℂ E)) :
    (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f hf)).ExactAt n :=
  rationalSheafComplex_exactAt_of_stalk_isZero _ n
    (fun y => closedComplexImmersion_supportedStalk_homology_isZero f hf hsmooth hdf y n hn)

/-- Rational singular cohomology with support in the actual full image of
a closed analytic immersion vanishes below twice its complex codimension.
All geometric hypotheses concern the literal map and its differential. -/
theorem closedComplexImmersion_supportCohomology_isZero
    (f : M → N) (hf : Topology.IsClosedEmbedding f)
    (hsmooth : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (n : ℕ) (hn : n < 2 * (Module.finrank ℂ F - Module.finrank ℂ E)) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ n) :=
  supportCohomology_isZero_of_stalk (TopCat.of N) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f hf)
    (2 * (Module.finrank ℂ F - Module.finrank ℂ E))
    (fun y q hq => closedComplexImmersion_supportedStalk_homology_isZero
      f hf hsmooth hdf y q hq) n hn

/-- The first possibly nonzero global supported cohomology group is
canonically the global sections of the genuine supported cohomology sheaf.
The required lower-degree vanishing is proved from the actual immersion. -/
def closedComplexImmersion_firstCohomologyIso
    (f : M → N) (hf : Topology.IsClosedEmbedding f)
    (hsmooth : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
        (2 * (Module.finrank ℂ F - Module.finrank ℂ E)) ≅
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f hf)).homology
          (2 * (Module.finrank ℂ F - Module.finrank ℂ E))).obj.obj (op ⊤) :=
  supportedGlobalFirstCohomologyIso_of_stalk (TopCat.of N) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f hf)
    (2 * (Module.finrank ℂ F - Module.finrank ℂ E))
    (fun y q hq => closedComplexImmersion_supportedStalk_homology_isZero
      f hf hsmooth hdf y q hq)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity
