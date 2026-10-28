import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections
import OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueSectionComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalAtlas
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalGermCompatibility
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalRecenter
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedGerms

/-! # Complex Thom -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexThom

noncomputable section

/-!
# A global rational Thom class for a closed complex immersion

The first constructions identify the canonical global relative-to-sheaf map
with the proved flasque edge isomorphism and lift actual sections through it.
The hypotheses in these general lemmas are explicit stalk-vanishing results;
they are not a definition of geometric purity or a postulated cycle map.

The final construction proves existence and uniqueness for an actual closed
complex-analytic immersion with injective manifold differential. The ambient
space is metrizable. Its restriction to every genuine differentiable normal
chart is the pullback of the fixed generator of the actual standard normal
group. No assertion of that generator's sign relative to a differential-form
volume convention is made here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

section General

variable (X : TopCat.{0}) [MetrizableSpace X] (O : Opens X) (d : ℕ)
  (hs : ∀ (x : X) (n : ℕ), n < d → IsZero
    ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) x).homology n))

include hs

/-- The relative flasque edge isomorphism is exactly the canonical map
obtained from the actual relative cochain comparison and section map. -/
theorem supportedGlobalFirstCohomologyIso_hom_eq_sectionMap :
    (GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk X O d hs).hom =
      RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) X O d := by
  unfold GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk
  rw [Iso.trans_hom, GlobalSupportPurity.Cycles.relativeSupportedGlobalCohomologyIso_hom]
  unfold GlobalSupportPurity.Cycles.supportedSheafGlobalFirstCohomologyIso_of_stalk
    GlobalSupportPurity.Cycles.rationalFlasqueFirstCohomologyIso_of_stalk
  rw [FlasqueSectionComparison.Cycles.rationalFlasqueFirstCohomologyIso_hom_eq_sectionMap]
  unfold AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections
  rw [HomologicalComplex.homologyMap_comp]
  unfold RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap
  rw [RelativeCohomologySections.Cycles.relativeCohomologySectionMap_def, Category.assoc]
  rfl

/-- Under proved lower stalk vanishing, the actual canonical global map
is invertible, with no choice of a comparison map. -/
theorem relativeCohomologyGlobalSectionMap_isIso :
    IsIso (RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) X O d) := by
  rw [← supportedGlobalFirstCohomologyIso_hom_eq_sectionMap X O d hs]
  infer_instance

/-- Lift a genuine global cohomology-sheaf section to the original-space
relative singular cohomology group via the proved edge isomorphism. -/
def supportedClassOfSection
    (s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.obj
      (op (⊤ : Opens X))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d :=
  (GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk X O d hs).inv s

/-- The lifted class has exactly the supplied section under the actual
global relative-to-supported map. -/
@[simp]
theorem supportedClassOfSection_image
    (s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.obj
      (op (⊤ : Opens X))) :
    RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) X O d
      (supportedClassOfSection X O d hs s) = s := by
  rw [← supportedGlobalFirstCohomologyIso_hom_eq_sectionMap X O d hs]
  exact (GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk X O d hs).toLinearEquiv.apply_symm_apply s

/-- The section completely determines the original relative class. -/
theorem supportedClassOfSection_unique
    (s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.obj
      (op (⊤ : Opens X)))
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d)
    (ha : RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) X O d a = s) :
    a = supportedClassOfSection X O d hs s := by
  apply (GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk X O d hs).toLinearEquiv.injective
  change (GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk X O d hs).hom a =
    (GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk X O d hs).hom
      (supportedClassOfSection X O d hs s)
  rw [supportedGlobalFirstCohomologyIso_hom_eq_sectionMap, ha,
    supportedClassOfSection_image]

/-- The actual lifting operation respects rational scaling. This makes
its dependence on the chosen primitive normal generator explicit. -/
theorem supportedClassOfSection_smul (q : ℚ)
    (s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.obj
      (op (⊤ : Opens X))) :
    supportedClassOfSection X O d hs (q • s) =
      q • supportedClassOfSection X O d hs s :=
  map_smul (GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk X O d hs).inv.hom q s

/-- On every actual open neighborhood, the lifted class produces the
restriction of the given global cohomology-sheaf section. -/
theorem supportedClassOfSection_restrict
    (s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.obj
      (op (⊤ : Opens X))) (U : Opens X) :
    RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) X O U d
      (RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X (O : Set X) U d
        (supportedClassOfSection X O d hs s)) =
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.map
        (homOfLE (le_top : U ≤ ⊤)).op s := by
  have h := ConcreteCategory.congr_hom
    (RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) X O U d)
    (supportedClassOfSection X O d hs s)
  simpa only [ConcreteCategory.comp_apply, supportedClassOfSection_image] using h.symm

omit hs in
/-- The actual supported image of a global relative class agrees with
specified local relative classes, and is zero on the open complement. -/
def HasSupportedLocalImages {ι : Type*} (U : ι → Opens X)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) d)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d) : Prop :=
  (∀ i, ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.map
      (homOfLE (le_top : U i ≤ ⊤)).op
      (RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) X O d b) =
    RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) X O (U i) d (a i)) ∧
  ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).homology d).obj.map
    (homOfLE (le_top : O ≤ ⊤)).op
    (RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) X O d b) = 0

omit hs [MetrizableSpace X] in
/-- Actual relative restriction equalities imply the corresponding
supported images; zero on the complement follows from the proved stalk
vanishing of the actual supported sheaf. -/
theorem hasSupportedLocalImages_of_restrictions
    {ι : Type*} (U : ι → Opens X)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) d)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d)
    (hb : ∀ i, RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X
      (O : Set X) (U i) d b = a i) : HasSupportedLocalImages X O d U a b := by
  constructor
  · intro i
    have h := ConcreteCategory.congr_hom
      (RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) X O (U i) d) b
    exact h.trans (congrArg (RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) X O (U i) d)
      (hb i))
  · apply SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) X O O d
    intro x hx hnot
    exact (hnot hx).elim

/-- Actual relative classes with compatible germs on a closed support
determine a unique global relative class in the first possible degree. -/
theorem existsUnique_supportedClass_of_germs_off_open
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U ⊔ O = ⊤)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) d)
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), x ∉ O →
      TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U i) x hi (a i) =
        TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U j) x hj (a j)) :
    ∃! b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d,
      HasSupportedLocalImages X O d U a b := by
  obtain ⟨s, hs_local, hs_unique⟩ :=
    NormalGermCompatibility.Cycles.existsUnique_relativeCohomologySection_of_germs_off_open
      (ModuleCat.of ℚ ℚ) X O U hcover d a ha
  refine ⟨supportedClassOfSection X O d hs s, ?_, ?_⟩
  · change (∀ i, _ = _) ∧ _ = 0
    simpa only [supportedClassOfSection_image] using hs_local
  · intro b hb
    apply supportedClassOfSection_unique X O d hs s b
    exact hs_unique _ hb

/-- The global class is selected from the proved unique lifting statement;
all gluing and lower-degree hypotheses remain explicit in this general API. -/
def supportedClassFromRelativeGerms
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U ⊔ O = ⊤)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) d)
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), x ∉ O →
      TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U i) x hi (a i) =
        TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U j) x hj (a j)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d :=
  Classical.choose (existsUnique_supportedClass_of_germs_off_open X O d hs U hcover a ha)

/-- The constructed global class has precisely the supplied local images. -/
theorem supportedClassFromRelativeGerms_hasLocalImages
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U ⊔ O = ⊤)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) d)
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), x ∉ O →
      TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U i) x hi (a i) =
        TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U j) x hj (a j)) :
    HasSupportedLocalImages X O d U a
      (supportedClassFromRelativeGerms X O d hs U hcover a ha) :=
  (Classical.choose_spec
    (existsUnique_supportedClass_of_germs_off_open X O d hs U hcover a ha)).1

/-- No other global relative class has these same local supported images. -/
theorem supportedClassFromRelativeGerms_unique
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U ⊔ O = ⊤)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) d)
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), x ∉ O →
      TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U i) x hi (a i) =
        TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X (O : Set X) d)
          (U j) x hj (a j))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) d)
    (hb : HasSupportedLocalImages X O d U a b) :
    b = supportedClassFromRelativeGerms X O d hs U hcover a ha :=
  (Classical.choose_spec
    (existsUnique_supportedClass_of_germs_off_open X O d hs U hcover a ha)).2 b hb

end General

open scoped _root_.Manifold ContDiff

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
  (he : Topology.IsClosedEmbedding f)

/-- The normalized class in the actual normal neighborhood supplied by
the inverse function theorem for this immersion. -/
def complexImmersionLocalClass (x : M) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of N) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he : Set N)
        (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x))
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  exact (ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he x).rationalClassFin

/-- The actual constructed ambient normal chart is complex differentiable
in both directions, as a consequence of the immersion normal form. -/
theorem complexImmersionNormalPair_mdifferentiable (x : M) :
    (ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he x).ambientChart.MDifferentiable
      𝓘(ℂ, F) 𝓘(ℂ, E × (Fin (ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) → ℂ)) :=
  ComplexPoints.Analytic.NormalCoordinatesDifferentiable.normalPairOfImmersion_ambientChart_mdifferentiable
    (ComplexNormalAtlas.Cycles.complexImmersion_standardComplement f hf hi x) he.isEmbedding (by simp)

/-- Normalized local classes agree as genuine relative-cohomology germs
at every support point in every overlap. Both the charts and their
differentiability are constructed from the original geometric hypotheses. -/
theorem complexImmersionLocalClass_germs
    (i j : M) (y : N)
    (hyi : y ∈ ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he i)
    (hyj : y ∈ ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he j)
    (hy : y ∉ EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he) :
    TopCat.Presheaf.germ
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
          (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he : Set N) (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F))
        (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he i) y hyi
        (complexImmersionLocalClass f hf hi he i) =
      TopCat.Presheaf.germ
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
          (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he : Set N) (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F))
        (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he j) y hyj
        (complexImmersionLocalClass f hf hi he j) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hymem : y ∈ Set.range f := by
    simpa only [EmbeddedSupportComplement.Cycles.mem_embeddedSupportComplement, not_not] using hy
  obtain ⟨z, rfl⟩ := hymem
  exact (ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he i).rationalClassFin_germ_eq_on_overlap
    (ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he j)
    (complexImmersionNormalPair_mdifferentiable f hf hi he i)
    (complexImmersionNormalPair_mdifferentiable f hf hi he j) z hyi hyj

variable [MetrizableSpace N]

/-- The global rational Thom class of the actual closed complex immersion,
normalized by the fixed primitive class in the standard complex normal
model. No local purity, chart compatibility, or class existence is assumed. -/
def complexThomClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) :=
  supportedClassFromRelativeGerms (TopCat.of N) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he)
    (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)
    (GlobalSupportPurity.Cycles.closedComplexImmersion_supportedStalk_homology_isZero f he hf hi)
    (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen_cover f hf hi he)
    (complexImmersionLocalClass f hf hi he) (complexImmersionLocalClass_germs f hf hi he)

/-- The constructed global Thom class has exactly the normalized local
supported images and vanishes on the actual open complement. -/
theorem complexThomClass_hasLocalImages :
    HasSupportedLocalImages (TopCat.of N) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he)
      (complexImmersionLocalClass f hf hi he) (complexThomClass f hf hi he) :=
  supportedClassFromRelativeGerms_hasLocalImages (TopCat.of N)
    (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he) (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)
    (GlobalSupportPurity.Cycles.closedComplexImmersion_supportedStalk_homology_isZero f he hf hi)
    (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen_cover f hf hi he)
    (complexImmersionLocalClass f hf hi he) (complexImmersionLocalClass_germs f hf hi he)

/-- The normalized local supported images uniquely determine the actual
global relative class. -/
theorem complexThomClass_unique_of_localImages
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F))
    (ha : HasSupportedLocalImages (TopCat.of N) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he)
      (complexImmersionLocalClass f hf hi he) a) :
    a = complexThomClass f hf hi he :=
  supportedClassFromRelativeGerms_unique (TopCat.of N)
    (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he) (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)
    (GlobalSupportPurity.Cycles.closedComplexImmersion_supportedStalk_homology_isZero f he hf hi)
    (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen_cover f hf hi he)
    (complexImmersionLocalClass f hf hi he) (complexImmersionLocalClass_germs f hf hi he) a ha

/-- Restriction of the global class to an actual normal neighborhood gives
the same section of the genuine cohomology sheaf as the local normal class. -/
theorem complexThomClass_restrict_section (x : M) :
    RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)
      (RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
        (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) (complexThomClass f hf hi he)) =
    RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) (complexImmersionLocalClass f hf hi he x) := by
  have h := ConcreteCategory.congr_hom
    (RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)) (complexThomClass f hf hi he)
  exact h.symm.trans ((complexThomClass_hasLocalImages f hf hi he).1 x)

/-- On every chosen normal neighborhood, the actual relative restriction
of the global class equals the normalized local class, not only its image
in an auxiliary sheaf. -/
theorem complexThomClass_restrict (x : M) :
    RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) (complexThomClass f hf hi he) =
        complexImmersionLocalClass f hf hi he x := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let P := ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he x
  apply (P.relativeCohomologyGermIso (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)).toLinearEquiv.injective
  apply (NormalGermCompatibility.Cycles.relativeCohomologySectionMap_germ_eq_iff ℚ (TopCat.of N)
    (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he)
    (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
    (f x) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen_contains f hf hi he x)
    (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen_contains f hf hi he x)
    (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) _ _).1
  exact congrArg
    (TopCat.Presheaf.germ
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he)).homology
        (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)).obj
      (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x) (f x)
      (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen_contains f hf hi he x))
    (complexThomClass_restrict_section f hf hi he x)

/-- Actual local relative-cohomology normalization uniquely determines
the global Thom class; no auxiliary zero-section hypothesis is needed. -/
theorem complexThomClass_unique
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F))
    (ha : ∀ x : M, RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) a = complexImmersionLocalClass f hf hi he x) :
    a = complexThomClass f hf hi he :=
  complexThomClass_unique_of_localImages f hf hi he a
    (hasSupportedLocalImages_of_restrictions (TopCat.of N) (EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he)
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he)
      (complexImmersionLocalClass f hf hi he) a ha)

/-- Existence and uniqueness of the genuinely normalized global relative
class for a closed complex immersion, with every local and global
cohomology group the actual singular group. -/
theorem existsUnique_complexThomClass :
    ∃! a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
        (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F),
      ∀ x : M, RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ (ComplexNormalAtlas.Cycles.complexImmersionNormalOpen f hf hi he x)
        (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) a = complexImmersionLocalClass f hf hi he x :=
  ⟨complexThomClass f hf hi he, complexThomClass_restrict f hf hi he,
    complexThomClass_unique f hf hi he⟩

/-- The class is normalized on every genuine differentiable normal pair,
independently of the normal charts selected by the construction. The
right side is the actual pullback of the fixed standard normal class. -/
theorem complexThomClass_restrict_normalPair (x : M)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin (ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) → ℂ) f x)
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, F) 𝓘(ℂ, E × (Fin (ComplexNormalAtlas.Cycles.complexImmersionCodimension E F) → ℂ))) :
    RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)
      (complexThomClass f hf hi he) =
        P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)
          (RationalLocalPurity.Cycles.complexNormalRationalDualClass (ComplexNormalAtlas.Cycles.complexImmersionCodimension E F)) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  rw [← P.rationalClassFin_eq_normalPullback]
  exact (ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he x).rationalClassFin_restriction_eq_of_charts
    P (complexImmersionNormalPair_mdifferentiable f hf hi he x) hP
    (complexThomClass f hf hi he) (complexThomClass_restrict f hf hi he x)

/-- A nonempty immersed support has a nonzero global class because its
actual restriction is a nonzero local normal class. -/
theorem complexThomClass_ne_zero (x : M) : complexThomClass f hf hi he ≠ 0 := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  exact (ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he x).relativeClass_ne_zero_of_normalization
    (complexThomClass f hf hi he) (complexThomClass_restrict f hf hi he x)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexThom
