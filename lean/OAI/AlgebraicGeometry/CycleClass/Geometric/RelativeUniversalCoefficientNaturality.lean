import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainD
import OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexNaturality

/-! # Relative Universal Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles

noncomputable section

/-!
# Naturality of relative evaluation and universal coefficients

The actual relative cochain kernel and relative chain cokernel have their
canonical maps for continuous maps of pairs. Their degreewise duality and
canonical pairing commute with those maps. Consequently the field
universal-coefficient equivalence and its inverse are natural for pairs.
-/

open _root_.CategoryTheory

section Evaluation

variable {R : Type} [CommRing R]

/-- Relative degreewise evaluation intertwines the actual maps of pair cochains
and pair chains. -/
theorem relativeDegreewiseChainDualEquiv_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y B).X n) :
    RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv M X A n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h).f n c) =
      (RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv M Y B n c).comp
        ((RelativeScalarChains.Cycles.relativeScalarChainsMap R f h).f n).hom := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A n z
  rw [RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection, LinearMap.comp_apply]
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality R f h) n) z
  change (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h).f n ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z) =
    (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y B).f n ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap f).f n z) at hp
  rw [hp, RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection]
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M f h) n) c
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h).f n c) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f n c) at hi
  rw [hi]
  exact LinearMap.congr_fun
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.degreewiseChainDualEquiv_pullback M (TopCat.toSSet.map f) n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f n c)) z

/-- The canonical identification of relative cochains with the dual complex
commutes with every continuous map of pairs. -/
theorem relativeCochainDualIso_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h ≫ (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom =
      (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom ≫
        DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M := by
  ext n c
  exact relativeDegreewiseChainDualEquiv_naturality M f h n c

/-- The same canonical square commutes on genuine categorical cohomology. -/
theorem relativeCochainDualIso_homology_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n ≫
        HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom n =
      HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom n ≫
        HomologicalComplex.homologyMap
          (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M) n := by
  change HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h) n ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relativeCochainDualIso_naturality]

/-- Relative cohomological pullback is adjoint to the actual relative homology
pushforward under canonical evaluation, in every degree. -/
theorem relativeHomologyEvaluation_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y B n) (z : RelativeScalarChains.Cycles.relativeScalarHomology R X A n) :
    RelativeChainD.Cycles.relativeHomologyEvaluation M X A n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c) z =
      RelativeChainD.Cycles.relativeHomologyEvaluation M Y B n c
        ((HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) n) z) := by
  have hi := ConcreteCategory.congr_hom
    (relativeCochainDualIso_homology_naturality M f h n) c
  change (HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom n)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c) =
    (HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M) n)
      ((HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom n) c) at hi
  change DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation (RelativeScalarChains.Cycles.relativeScalarChains R X A) M n
      ((HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom n)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c)) z = _
  rw [hi]
  exact DualComplexNaturality.Cycles.linearHomHomologyEvaluation_naturality (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M n
    ((HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom n) c) z

/-- Pair-map naturality as equality of linear functionals on relative homology. -/
theorem relativeHomologyEvaluation_naturality_linearMap (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y B n) :
    RelativeChainD.Cycles.relativeHomologyEvaluation M X A n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c) =
      (RelativeChainD.Cycles.relativeHomologyEvaluation M Y B n c).comp
        (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) n).hom := by
  ext z
  exact relativeHomologyEvaluation_naturality M f h n c z

end Evaluation

variable (F : Type) [Field F]

/-- The field universal-coefficient equivalence for actual relative singular
cohomology is natural for all continuous maps of pairs. -/
theorem relativeUniversalCoefficientEquiv_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) Y B n) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F X A n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of F F) f h n) c) =
      (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F Y B n c).comp
        (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap F f h) n).hom :=
  relativeHomologyEvaluation_naturality_linearMap (ModuleCat.of F F) f h n c

/-- The inverse relative universal-coefficient equivalence also respects maps
of pairs; no choice of extending a functional affects this identity. -/
theorem relativeUniversalCoefficientEquiv_symm_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) (L : Module.Dual F (RelativeScalarChains.Cycles.relativeScalarHomology F Y B n)) :
    (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F X A n).symm
        (L.comp (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap F f h) n).hom) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of F F) f h n)
        ((RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F Y B n).symm L) := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F X A n).injective
  rw [LinearEquiv.apply_symm_apply, relativeUniversalCoefficientEquiv_naturality,
    LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles
