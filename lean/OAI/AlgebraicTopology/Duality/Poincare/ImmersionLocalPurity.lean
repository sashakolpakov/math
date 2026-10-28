import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicImmersionNormalPair
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

/-! # Immersion Local Purity -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

noncomputable section

/-!
# Local relative cohomology of genuine embedded normal pairs

The coordinate maps in this file are actual homeomorphisms of pairs. Their
pullbacks identify the kernel-defined relative singular cochain complexes.
Normal neighborhoods are constructed from genuine manifold immersions and
topological embeddings; their removed subspaces are the complements of the
full embedded image.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)

/-- A genuine homeomorphism of pairs induces an isomorphism of the actual
relative singular cochain kernels, by pullback in both directions. -/
def relativePairHomeomorphCochainIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains A Y T ≅ Cohomology.Singular.RelativeSequence.relativeSingularCochains A X S := by
  let f : X ⟶ Y := (TopCat.isoOfHomeo e).hom
  let g : Y ⟶ X := (TopCat.isoOfHomeo e).inv
  have hf : Set.MapsTo f S T := fun x hx => (h x).mp hx
  have hg : Set.MapsTo g T S := by
    intro y hy
    apply (h (e.symm y)).mpr
    simpa only [e.apply_symm_apply] using hy
  exact {
    hom := Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A f hf
    inv := Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A g hg
    hom_inv_id := Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id A g f hg hf
      (TopCat.isoOfHomeo e).inv_hom_id
    inv_hom_id := Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id A f g hf hg
      (TopCat.isoOfHomeo e).hom_inv_id }

@[simp]
theorem relativePairHomeomorphCochainIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    (relativePairHomeomorphCochainIso A e S T h).hom =
      Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A (TopCat.isoOfHomeo e).hom
        (fun x hx => (h x).mp hx) := rfl

/-- The corresponding genuine relative-cohomology isomorphism. -/
def relativePairHomeomorphCohomologyIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology A Y T n ≅ Cohomology.Singular.RelativeSequence.relativeSingularCohomology A X S n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (relativePairHomeomorphCochainIso A e S T h)

@[simp]
theorem relativePairHomeomorphCohomologyIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) (n : ℕ) :
    (relativePairHomeomorphCohomologyIso A e S T h n).hom =
      Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap A (TopCat.isoOfHomeo e).hom
        (fun x hx => (h x).mp hx) n := rfl

end

namespace Analytic.ImmersionNormalPair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

/-- The removed subset is exactly the complement of the full embedded image
inside the genuine coordinate neighborhood. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeComplement : Set P.neighborhood :=
  {y | y.val ∉ Set.range f}

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)

/-- Actual relative singular cohomology with support in the embedded image,
computed in this actual ambient coordinate neighborhood. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology (n : ℕ) : ModuleCat.{0} R :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomology A (TopCat.of P.neighborhood) P.relativeComplement n

/-- The actual normal coordinate, as a continuous map into the full normal
vector space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate : TopCat.of P.neighborhood ⟶ TopCat.of F :=
  TopCat.ofHom ⟨fun y => (P.homeomorph y).2.val,
    continuous_subtype_val.comp (continuous_snd.comp P.homeomorph.continuous)⟩

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_apply (y : P.neighborhood) :
    P.normalCoordinate y = (P.ambientChart y.val).2 := rfl

/-- The coordinate map factors through the product of balls by its actual
normal projection and the actual open-ball inclusion. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_eq :
    P.normalCoordinate = (TopCat.isoOfHomeo P.homeomorph).hom ≫
      AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) P.radius)
        (Metric.ball (0 : F) P.radius) ≫
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of F) (Metric.ball (0 : F) P.radius) := rfl

/-- The normal coordinate sends the actual removed subspace into the
punctured normal vector space. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_mapsTo :
    Set.MapsTo P.normalCoordinate P.relativeComplement ({0}ᶜ : Set F) :=
  fun y hy => (P.mem_complement_iff y).mp hy

/-- Pullback of relative cochains along the actual normal coordinate. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCochainPullback :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains A (TopCat.of F) ({0}ᶜ : Set F) ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCochains A (TopCat.of P.neighborhood) P.relativeComplement :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A P.normalCoordinate P.normalCoordinate_mapsTo

/-- The canonical relative-cohomology pullback whose invertibility expresses
local purity in this coordinate neighborhood. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology A (TopCat.of F) ({0}ᶜ : Set F) n ⟶
      P.relativeCohomology A n :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap A P.normalCoordinate P.normalCoordinate_mapsTo n

/-- The exact pair condition for the normal-coordinate homeomorphism. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.homeomorph_mem_relativeComplement (y : P.neighborhood) :
    y ∈ P.relativeComplement ↔
      P.homeomorph y ∈ AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductComplement
        (Metric.ball (0 : E) P.radius) (Metric.ball (0 : F) P.radius)
        ⟨0, Metric.mem_ball_self P.radius_pos⟩ := by
  change y.val ∉ Set.range f ↔
    (P.homeomorph y).2 ≠ ⟨0, Metric.mem_ball_self P.radius_pos⟩
  rw [P.mem_complement_iff y]
  constructor
  · intro hy hzero
    exact hy (congrArg Subtype.val hzero)
  · intro hy hzero
    exact hy (Subtype.ext hzero)

/-- Normal coordinates identify the actual relative cochain complexes. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCochainIso :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains A
        (TopCat.of (Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius))
        (AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) P.radius)
          (Metric.ball (0 : F) P.radius) ⟨0, Metric.mem_ball_self P.radius_pos⟩) ≅
      Cohomology.Singular.RelativeSequence.relativeSingularCochains A (TopCat.of P.neighborhood) P.relativeComplement :=
  relativePairHomeomorphCochainIso A P.homeomorph _ _
    P.homeomorph_mem_relativeComplement

/-- The corresponding relative-cohomology comparison is the actual
pullback along the normal-coordinate homeomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCohomologyIso (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology A
        (TopCat.of (Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius))
        (AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) P.radius)
          (Metric.ball (0 : F) P.radius) ⟨0, Metric.mem_ball_self P.radius_pos⟩) n ≅
      P.relativeCohomology A n :=
  relativePairHomeomorphCohomologyIso A P.homeomorph _ _
    P.homeomorph_mem_relativeComplement n

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCohomologyIso_hom (n : ℕ) :
    (P.ballPairCohomologyIso A n).hom =
      Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap A (TopCat.isoOfHomeo P.homeomorph).hom
        (fun y hy => (P.homeomorph_mem_relativeComplement y).mp hy) n := rfl

/-- Shrinking an actual normal neighborhood while retaining its chart does
not change the underlying normal-coordinate map. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_comp_neighborhoodInclusion (Q : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N)) hQP ≫ P.normalCoordinate = Q.normalCoordinate := by
  ext y
  change (P.ambientChart y.val).2 = (Q.ambientChart y.val).2
  rw [hchart]

/-- The normal-coordinate pullback commutes with the actual relative
cohomology restriction to a smaller neighborhood with the same chart. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap_restrict (Q : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart)
    (n : ℕ) :
    P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫
        AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n =
      Q.normalCohomologyMap (ModuleCat.of ℚ ℚ) n := by
  change Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) P.normalCoordinate
      P.normalCoordinate_mapsTo n ≫
    Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N)) hQP) (fun _ hx => hx) n = _
  rw [Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  unfold AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
  congr 1
  exact P.normalCoordinate_comp_neighborhoodInclusion Q hQP hchart

variable [NormedSpace ℝ E]

/-- Actual normal projection identifies relative rational cohomology of the
embedded-support neighborhood with punctured-normal cohomology. Its two steps
are normal-ball excision and the actual pair-coordinate homeomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyIso (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      P.relativeCohomology (ModuleCat.of ℚ ℚ) n :=
  AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso E F P.radius P.radius P.radius_pos P.radius_pos n ≪≫
    P.ballPairCohomologyIso (ModuleCat.of ℚ ℚ) n

/-- The comparison is precisely pullback along the actual normal coordinate. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyIso_hom (n : ℕ) :
    (P.relativeCohomologyIso n).hom = P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n := by
  change (AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso E F P.radius P.radius
      P.radius_pos P.radius_pos n).hom ≫
    (P.ballPairCohomologyIso (ModuleCat.of ℚ ℚ) n).hom = _
  rw [AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso_hom, AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCohomologyIso_hom]
  unfold AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyMap AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
  rw [Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap_isIso (n : ℕ) :
    IsIso (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n) := by
  rw [← P.relativeCohomologyIso_hom n]
  infer_instance

variable [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual top rational cohomology of the local support pair is one
dimensional, normalized by the established complex normal-space calculation. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalTopCohomologyIso :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F) ≅ ModuleCat.of ℚ ℚ :=
  (P.relativeCohomologyIso (2 * Module.finrank ℂ F)).symm ≪≫
    AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso F

/-- The chart-normalized local class is the inverse image of one under the
proved top cohomology isomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F) :=
  P.rationalTopCohomologyIso.inv 1

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_normalization : P.rationalTopCohomologyIso.hom P.rationalClass = 1 :=
  P.rationalTopCohomologyIso.toLinearEquiv.apply_symm_apply 1

/-- This class is literally the pullback of the normalized complex normal
class along the actual second coordinate. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_eq_pullback :
    P.rationalClass = P.normalCohomologyMap (ModuleCat.of ℚ ℚ)
      (2 * Module.finrank ℂ F) (AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F) := by
  rw [← P.relativeCohomologyIso_hom]
  rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_ne_zero : P.rationalClass ≠ 0 := by
  intro h
  have hn := P.rationalClass_normalization
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Normalization one uniquely specifies the local class in this chart. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_unique
    (a : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F))
    (ha : P.rationalTopCohomologyIso.hom a = 1) : a = P.rationalClass := by
  apply P.rationalTopCohomologyIso.toLinearEquiv.injective
  exact ha.trans P.rationalClass_normalization.symm

/-- Every top local class is a unique rational multiple of the normalized class. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_generates
    (a : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F)) :
    ∃! q : ℚ, q • P.rationalClass = a := by
  let e := P.rationalTopCohomologyIso.toLinearEquiv
  have hnorm (q : ℚ) : e (q • P.rationalClass) = q := by
    rw [map_smul]
    change q • P.rationalTopCohomologyIso.hom P.rationalClass = q
    rw [P.rationalClass_normalization]
    exact mul_one q
  refine ⟨e a, ?_, ?_⟩
  · apply e.injective
    exact hnorm _
  · intro q hq
    exact (hnorm q).symm.trans (congrArg e hq)

/-- All non-normal degrees vanish, for the actual embedded-support pair. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology_isZero (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ F) :
    IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n) :=
  (AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology_isZero F n hn).of_iso (P.relativeCohomologyIso n).symm

/-- In particular local support cohomology vanishes below real codimension. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology_isZero_of_lt (n : ℕ) (hn : n < 2 * Module.finrank ℂ F) :
    IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n) :=
  P.relativeCohomology_isZero n (Nat.ne_of_lt hn)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology_isZero_iff (n : ℕ) :
    IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n) ↔ n ≠ 2 * Module.finrank ℂ F := by
  refine ⟨?_, P.relativeCohomology_isZero n⟩
  intro hz hn
  subst n
  let : Subsingleton (P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F)) :=
    ModuleCat.subsingleton_of_isZero hz
  exact P.rationalClass_ne_zero (Subsingleton.elim _ _)

/-- The normalized class restricts to the normalized class on every smaller
normal neighborhood with the same actual chart. This is local compatibility;
no compatibility between different normal charts is assumed. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_restrict (Q : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f)
        (2 * Module.finrank ℂ F) P.rationalClass = Q.rationalClass := by
  rw [P.rationalClass_eq_pullback, Q.rationalClass_eq_pullback]
  exact ConcreteCategory.congr_hom
    (P.normalCohomologyMap_restrict Q hQP hchart (2 * Module.finrank ℂ F))
      (AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F)

end Analytic.ImmersionNormalPair

namespace DimensionCycleSupport

variable {V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The genuine relative rational cohomology in the chosen normal
neighborhood of a regular point of an algebraic cycle support. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalCohomology (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (n : ℕ) : ModuleCat.{0} ℚ :=
  (Z.regularComplementNormalPair x).relativeCohomology (ModuleCat.of ℚ ℚ) n

/-- The removed subset in this relative cohomology is exactly the complement
of the original algebraic cycle's analytic support in the chosen neighborhood. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRelativeComplement_eq (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (Z.regularComplementNormalPair x).relativeComplement =
      {y : (Z.regularComplementNormalPair x).neighborhood |
        (y.val : V.analyticSpace) ∉ Set.range Z.analyticInclusion} := by
  ext y
  change y.val ∉ Set.range Z.regularComplementInclusion ↔ _
  rw [Z.range_regularComplementInclusion]
  rfl

/-- The actual local relative rational cohomology vanishes outside degree
`2p`, where `p` is the algebraic cycle's proved complex codimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalCohomology_isZero (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (Z.regularLocalRationalCohomology x n) := by
  apply (Z.regularComplementNormalPair x).relativeCohomology_isZero n
  simpa only [Z.regularComplementChartComplement_complex_finrank x] using hn

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalCohomology_isZero_of_lt (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (n : ℕ) (hn : n < 2 * p) :
    IsZero (Z.regularLocalRationalCohomology x n) :=
  Z.regularLocalRationalCohomology_isZero x n (Nat.ne_of_lt hn)

/-- Local purity in its precise zero/nonzero form for an actual cycle's
regular locus inside the complement of the singular boundary. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalCohomology_isZero_iff (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (n : ℕ) :
    IsZero (Z.regularLocalRationalCohomology x n) ↔ n ≠ 2 * p := by
  simpa only [Z.regularComplementChartComplement_complex_finrank x] using
    (Z.regularComplementNormalPair x).relativeCohomology_isZero_iff n

/-- The top local group is rational one-dimensional with the normalization
coming from the actual complex normal coordinates. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalTopCohomologyIso (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Z.regularLocalRationalCohomology x (2 * p) ≅ ModuleCat.of ℚ ℚ := by
  simpa only [Z.regularComplementChartComplement_complex_finrank x] using
    (Z.regularComplementNormalPair x).rationalTopCohomologyIso

/-- The chart-normalized rational local class of the actual algebraic support. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalClass (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Z.regularLocalRationalCohomology x (2 * p) :=
  (Z.regularLocalRationalTopCohomologyIso x).inv 1

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalClass_normalization (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (Z.regularLocalRationalTopCohomologyIso x).hom (Z.regularLocalRationalClass x) = 1 :=
  (Z.regularLocalRationalTopCohomologyIso x).toLinearEquiv.apply_symm_apply 1

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocalRationalClass_ne_zero (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Z.regularLocalRationalClass x ≠ 0 := by
  intro h
  have hn := Z.regularLocalRationalClass_normalization x
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every neighborhood of a regular support point contains a genuine normal
pair with the proved local purity and top-degree computation. The pair is
constructed from the actual immersion, not supplied as extra geometric data. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.exists_regularLocalRationalPurity (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (U : Set Z.regularAmbientSpace)
    (hU : U ∈ nhds (Z.regularComplementInclusion x)) :
    ∃ P : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel
        (Z.RegularComplementChartComplement x) Z.regularComplementInclusion x,
      P.ambientChart = (Z.regularComplementNormalPair x).ambientChart ∧
      P.neighborhood ⊆ U ∧
      (∀ n : ℕ, n < 2 * p →
        IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n)) ∧
      Nonempty (P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * p) ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨P, hchart, hP⟩ := Z.regularComplementNormalPair_cofinal x U hU
  refine ⟨P, hchart, hP, ?_, ?_⟩
  · intro n hn
    apply P.relativeCohomology_isZero_of_lt n
    simpa only [Z.regularComplementChartComplement_complex_finrank x] using hn
  · exact ⟨by
      simpa only [Z.regularComplementChartComplement_complex_finrank x] using
        P.rationalTopCohomologyIso⟩

end DimensionCycleSupport

end

end OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity
