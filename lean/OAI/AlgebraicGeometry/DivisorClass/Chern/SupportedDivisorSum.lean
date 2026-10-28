import OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteDetection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Component
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality

/-! # Supported Divisor Sum -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum
section

/-!
# ChernClass: the genuine supported Thom class of the actual finite divisor

Each codimension-one support has the previously constructed supported
cycle class. Its support lies outside the reference open. Enlarge support
by the actual map of pairs and sum with the actual algebraic integer orders.
This construction does not identify Thom classes with geometric trace classes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

/-- The given integral presentation, in the existing integral-variety interface. -/
def integralPresentationVariety (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨X, inferInstance⟩

end Construction

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen
local notation "V" => OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.Construction.integralPresentationVariety X

/-- The same point closure, with the established dimension grading. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceDivisorSupport (z : L.ReferenceDivisorPoint) : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1 :=
  Component.Construction.integralSupportToVariety V 1 (Geometric.Construction.pointDivisorSupport X ⟨z.val, z.property.1⟩)

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceDivisorSupport_injective : Function.Injective L.referenceDivisorSupport := by
  intro z w h
  apply Subtype.ext
  apply irreducibleSetEquivPoints.symm.injective
  exact congrArg (fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1 => Z.val) h

/-- Its actual complex support misses the reference open. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceDivisorSupport_complement (z : L.ReferenceDivisorPoint) :
    (O : Set T) ⊆ (Set.range (L.referenceDivisorSupport z).analyticInclusion)ᶜ := by
  intro x hx hZ
  rw [(L.referenceDivisorSupport z).range_analyticInclusion] at hZ
  have hs : closure ({z.val} : Set X.carrier) ⊆ (L.rationalReferenceOpen : Set X.carrier)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr z.property.2) L.rationalReferenceOpen.isOpen.isClosed_compl
  exact hs hZ hx

/-- The original supported cycle class, enlarged to the actual reference support. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceDivisorSupportedClass (z : L.ReferenceDivisorPoint) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T)
    (L.referenceDivisorSupport_complement z) 2 (L.referenceDivisorSupport z).rationalSupportedCycleClass

/-- Forgetting the enlarged support recovers the original absolute Thom cycle class. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceDivisorSupportedClass_absolute (z : L.ReferenceDivisorPoint) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T (O : Set T) 2
      (L.referenceDivisorSupportedClass z) = (L.referenceDivisorSupport z).rationalCycleClass := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (𝟙 T)
      (L.referenceDivisorSupport_complement z) 2) (L.referenceDivisorSupport z).rationalSupportedCycleClass
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, Category.comp_id] at h
  exact h

local instance : Fintype L.ReferenceDivisorPoint := Fintype.ofFinite _

/-- Sum the genuine supported cycle classes with their original algebraic orders. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 :=
  ∑ z : L.ReferenceDivisorPoint, (L.rationalSectionOrder z.val : ℚ) • L.referenceDivisorSupportedClass z

/-- The same finite divisor in the existing integral-variety cycle interface. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomCycle : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1 :=
  ∑ z : L.ReferenceDivisorPoint,
    Finsupp.single (L.referenceDivisorSupport z) (L.rationalSectionOrder z.val : ℚ)

/-- The supported sum forgets to the previously defined Thom cycle-class
map applied to the same finite actual divisor. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomClass_absolute :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T (O : Set T) 2 L.rationalSectionDivisorThomClass =
      (V).rationalCycleClass 1 L.rationalSectionDivisorThomCycle := by
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomClass Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomCycle
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, L.referenceDivisorSupportedClass_absolute, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass_single]

/-- Every support coefficient is exactly its previously defined algebraic order. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomCycle_apply (z : L.ReferenceDivisorPoint) :
    L.rationalSectionDivisorThomCycle (L.referenceDivisorSupport z) = (L.rationalSectionOrder z.val : ℚ) := by
  classical
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomCycle
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single z]
  · exact Finsupp.single_eq_same
  · intro w _ hw
    exact Finsupp.single_eq_of_ne (fun h => hw (L.referenceDivisorSupport_injective h.symm))
  · simp

end AlgebraicLineBundle

end

/-!
# ChernClass: the supported divisor sum uses precisely the original divisor

The finite sum over reference divisor points is proved equal to the
already-constructed dimension-graded integral divisor. Rationalization and
the existing integral-variety support identification give the exact cycle
appearing in the supported Thom sum.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local instance : Fintype L.ReferenceDivisorPoint := Fintype.ofFinite _

/-- The previously constructed integral divisor is exactly this finite
sum, including zero coefficients and all supports outside the sum. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionIntegralDivisor_eq_reference_sum :
    L.rationalSectionIntegralDivisor =
      ∑ z : L.ReferenceDivisorPoint,
        Finsupp.single (Geometric.Construction.pointDivisorSupport X ⟨z.val, z.property.1⟩)
          (L.rationalSectionOrder z.val) := by
  classical
  ext Z
  rw [Finsupp.finsetSum_apply]
  by_cases hZ : Z ∈ Set.range (Geometric.Construction.pointDivisorSupport X)
  · obtain ⟨z, rfl⟩ := hZ
    rw [L.rationalSectionIntegralDivisor_apply]
    by_cases hz : z.val ∈ L.rationalReferenceOpen
    · rw [L.rationalSectionOrder_zero_on_reference z.val hz]
      symm
      apply Finset.sum_eq_zero
      intro w _
      apply Finsupp.single_eq_of_ne
      intro he
      have hp := congrArg Subtype.val (Geometric.Construction.pointDivisorSupport_injective X he)
      exact w.property.2 (hp ▸ hz)
    · let w : L.ReferenceDivisorPoint := ⟨z.val, z.property, hz⟩
      rw [Finset.sum_eq_single w]
      · exact Finsupp.single_eq_same.symm
      · intro u _ huw
        apply Finsupp.single_eq_of_ne
        intro he
        have hp := congrArg Subtype.val (Geometric.Construction.pointDivisorSupport_injective X he)
        exact huw (Subtype.ext hp.symm)
      · simp
  · change Finsupp.mapDomain (Geometric.Construction.pointDivisorSupport X)
      (Finsupp.subtypeDomain (fun z : X.carrier => Order.coheight z = 1)
        L.rationalSectionPointDivisor) Z = _
    rw [Finsupp.mapDomain_of_notMem_range _ Z hZ]
    symm
    apply Finset.sum_eq_zero
    intro z _
    exact Finsupp.single_eq_of_ne (fun he => hZ ⟨⟨z.val, z.property.1⟩, he.symm⟩)

/-- The finite cycle in the Thom-class construction is the original
integral divisor with its coefficients rationalized and supports identified. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomCycle_eq_actual :
    L.rationalSectionDivisorThomCycle =
      Finsupp.mapDomain
        (Component.Construction.integralSupportToVariety (Construction.integralPresentationVariety X) 1)
        (Classes.Construction.rationalizeDivisor X L.rationalSectionIntegralDivisor) := by
  classical
  rw [L.rationalSectionIntegralDivisor_eq_reference_sum, map_sum, Finsupp.mapDomain_finsetSum]
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomCycle
  apply Finset.sum_congr rfl
  intro z _
  rw [Classes.Construction.rationalizeDivisor_single, Finsupp.mapDomain_single]
  rfl

/-- Forget support from the actual divisor's supported Thom sum. The
right side contains the original divisor, not a replacement cycle. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomClass_absolute_actual :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
      (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2
      L.rationalSectionDivisorThomClass =
    (Construction.integralPresentationVariety X).rationalCycleClass 1
      (Finsupp.mapDomain
        (Component.Construction.integralSupportToVariety (Construction.integralPresentationVariety X) 1)
        (Classes.Construction.rationalizeDivisor X L.rationalSectionIntegralDivisor)) := by
  rw [← L.rationalSectionDivisorThomCycle_eq_actual]
  exact L.rationalSectionDivisorThomClass_absolute

end AlgebraicLineBundle

end AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

namespace AlgebraicGeometry.DivisorClass.Chern

/-!
# ChernClass: isolate each actual reference divisor support

Distinct codimension-one point closures do not contain each other's
generic points. The finite set of reference divisor points therefore gives
an actual algebraic neighborhood excluding every other divisor support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

/-- Distinct actual divisor points cannot lie in each other's point closures. -/
theorem Line.Bundles.AlgebraicLineBundle.referenceDivisorPoint_not_mem_other_support (z w : L.ReferenceDivisorPoint) (hzw : z ≠ w) :
    z.val ∉ closure ({w.val} : Set X.carrier) := by
  intro hz
  let A : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm z.val
  let B : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm w.val
  have hAB : A ≤ B := closure_minimal (Set.singleton_subset_iff.mpr hz) B.isClosed
  have hne : A ≠ B := by
    intro he
    apply hzw
    exact Subtype.ext (irreducibleSetEquivPoints.symm.injective he)
  have hc := Order.coheight_add_one_le (lt_of_le_of_ne hAB hne)
  have hA : Order.coheight A = 1 := by
    simpa only [A, Order.coheight_orderIso] using z.property.1
  have hB : Order.coheight B = 1 := by
    simpa only [B, Order.coheight_orderIso] using w.property.1
  rw [hA, hB] at hc
  exact (by decide : ¬ (1 : ℕ∞) + 1 ≤ 1) hc

/-- The actual complement of one algebraic divisor support. -/
def Line.Bundles.AlgebraicLineBundle.referenceDivisorSupportComplement (w : L.ReferenceDivisorPoint) : X.carrier.Opens :=
  ⟨(closure ({w.val} : Set X.carrier))ᶜ, isClosed_closure.isOpen_compl⟩

/-- A finite intersection of actual open complements isolates the chosen support. -/
def Line.Bundles.AlgebraicLineBundle.referenceDivisorIsolatingOpen (z : L.ReferenceDivisorPoint) : X.carrier.Opens := by
  classical
  exact ⨅ w : L.ReferenceDivisorPoint, if w = z then ⊤ else L.referenceDivisorSupportComplement w

theorem Line.Bundles.AlgebraicLineBundle.referenceDivisorPoint_mem_isolatingOpen (z : L.ReferenceDivisorPoint) :
    z.val ∈ L.referenceDivisorIsolatingOpen z := by
  classical
  change z.val ∈ (⨅ w : L.ReferenceDivisorPoint,
    if w = z then ⊤ else L.referenceDivisorSupportComplement w : X.carrier.Opens)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  intro w
  by_cases hw : w = z
  · rw [ite_eq_left hw]
    trivial
  · rw [ite_eq_right hw]
    exact L.referenceDivisorPoint_not_mem_other_support z w (Ne.symm hw)

theorem Line.Bundles.AlgebraicLineBundle.referenceDivisorIsolatingOpen_subset_other_complement
    (z w : L.ReferenceDivisorPoint) (hzw : z ≠ w) :
    L.referenceDivisorIsolatingOpen z ≤ L.referenceDivisorSupportComplement w := by
  classical
  have h := iInf_le (fun v : L.ReferenceDivisorPoint =>
    if v = z then (⊤ : X.carrier.Opens) else L.referenceDivisorSupportComplement v) w
  rw [ite_eq_right (Ne.symm hzw)] at h
  exact h

end

/-- A pair map whose entire image lies in the target complement induces
zero on relative cohomology, by factorization through empty support. -/
theorem SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset {R : Type} [Ring R] (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) (h : ∀ x, f x ∈ B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hf n = 0 := by
  have hz : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X Set.univ n) := by
    simpa only [Set.compl_empty] using CycleClass.Geometric.ClosedSupportFiltration.Cycles.cohomologyWithEmptySupport_isZero M X n
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp M (𝟙 X) f
    (A := A) (B := Set.univ) (C := B) (fun _ _ => Set.mem_univ _) (fun x _ => h x) n
  have hc' : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f (A := Set.univ) (fun x _ => h x) n ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (𝟙 X) (A := A) (B := Set.univ) (fun _ _ => Set.mem_univ _) n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hf n := by
    simpa only [Category.id_comp] using hc
  rw [← hc', hz.eq_of_tgt (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f (fun x _ => h x) n) 0, zero_comp]

end AlgebraicGeometry.DivisorClass.Chern

namespace AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-!
# ChernClass: restrict the actual supported divisor sum to one support

The actual relative cycle class vanishes away from its support. In the
constructed isolating open all other summands therefore vanish, leaving
exactly the original algebraic coefficient times the chosen support class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

/-- Restriction away from the actual point closure annihilates its
original supported cycle class after reference-support enlargement. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceDivisorSupportedClass_restrict_away (z : L.ReferenceDivisorPoint)
    (U : X.carrier.Opens) (hU : U ≤ L.referenceDivisorSupportComplement z) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
      (L.referenceDivisorSupportedClass z) = 0 := by
  let f := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set T)
  let ha : Set.MapsTo f (L.analyticReferenceLocus (Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (O : Set T) := fun _ hx => hx
  have hr : ∀ x, f x ∈ (Set.range (L.referenceDivisorSupport z).analyticInclusion)ᶜ := by
    intro x
    rw [(L.referenceDivisorSupport z).range_analyticInclusion]
    exact hU x.property
  have hz := relativeCohomologyMap_zero_of_range_subset (ModuleCat.of ℚ ℚ) f
    (L.analyticReferenceLocus (Line.Bundles.AlgebraicLineBundle.analyticOpen X U))
    (Set.range (L.referenceDivisorSupport z).analyticInclusion)ᶜ
    (fun _ hx => L.referenceDivisorSupport_complement z (ha hx)) hr 2
  have hc : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T)
      (L.referenceDivisorSupport_complement z) 2 ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f ha 2 =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (fun _ hx => L.referenceDivisorSupport_complement z (ha hx)) 2 := by
    simpa only [Category.comp_id] using AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp
      (ModuleCat.of ℚ ℚ) f (𝟙 T) ha (L.referenceDivisorSupport_complement z) 2
  have hv := ConcreteCategory.congr_hom hc (L.referenceDivisorSupport z).rationalSupportedCycleClass
  rw [hz] at hv
  exact hv

local instance : Fintype L.ReferenceDivisorPoint := Fintype.ofFinite _

/-- The actual divisor sum has just its original coefficient in a
neighborhood isolating one reference divisor support. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomClass_restrict_isolated (z : L.ReferenceDivisorPoint)
    (U : X.carrier.Opens) (hU : U ≤ L.referenceDivisorIsolatingOpen z) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
      L.rationalSectionDivisorThomClass =
      (L.rationalSectionOrder z.val : ℚ) •
        CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
          (L.referenceDivisorSupportedClass z) := by
  classical
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionDivisorThomClass
  rw [map_sum, Finset.sum_eq_single z]
  · exact map_smul _ _ _
  · intro w _ hw
    rw [map_smul, L.referenceDivisorSupportedClass_restrict_away w U
      (hU.trans (L.referenceDivisorIsolatingOpen_subset_other_complement z w (Ne.symm hw))), smul_zero]
  · simp

end AlgebraicLineBundle

end AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

end

end OAI
