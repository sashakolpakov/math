import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PrincipalDivisor
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-! # Divisor Isolation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.DivisorIsolation

noncomputable section

/-! Isolate each of the finitely many actual divisor supports and restrict
the sum to its original algebraic coefficient times its cycle class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.AlgebraicLineBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.DivisorDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PrincipalDivisor.Constructions
variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (R : X.carrier.Opens) [Nonempty R]
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R

omit [IsIntegral X.carrier] [Nonempty R] in
/-- Distinct actual divisor points cannot lie in each other's point closures. -/
theorem complementDivisorPoint_not_mem_other_support (z w : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) (hzw : z ≠ w) :
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
def complementDivisorSupportComplement (w : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) : X.carrier.Opens :=
  ⟨(closure ({w.val} : Set X.carrier))ᶜ, isClosed_closure.isOpen_compl⟩

/-- A finite intersection of actual open complements isolates the chosen support. -/
def complementDivisorIsolatingOpen (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) : X.carrier.Opens := by
  classical
  exact ⨅ w : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R), if w = z then ⊤ else complementDivisorSupportComplement X R w

theorem complementDivisorPoint_mem_isolatingOpen (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) :
    z.val ∈ complementDivisorIsolatingOpen X R z := by
  classical
  change z.val ∈ (⨅ w : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R),
    if w = z then ⊤ else complementDivisorSupportComplement X R w : X.carrier.Opens)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  intro w
  by_cases hw : w = z
  · rw [ite_eq_left hw]
    trivial
  · rw [ite_eq_right hw]
    exact complementDivisorPoint_not_mem_other_support X R z w (Ne.symm hw)

omit [IsIntegral X.carrier] [Nonempty R] in
theorem complementDivisorIsolatingOpen_subset_other_complement
    (z w : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) (hzw : z ≠ w) :
    complementDivisorIsolatingOpen X R z ≤ complementDivisorSupportComplement X R w := by
  classical
  have h := iInf_le (fun v : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R) =>
    if v = z then (⊤ : X.carrier.Opens) else complementDivisorSupportComplement X R v) w
  rw [ite_eq_right (Ne.symm hzw)] at h
  exact h

omit [Nonempty R] in
/-- Restriction away from the actual point closure annihilates its
original supported cycle class after reference-support enlargement. -/
theorem complementDivisorSupportedClass_restrict_away (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R))
    (U : X.carrier.Opens) (hU : U ≤ complementDivisorSupportComplement X R z) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
      (Supported.PrincipalDivisor.Constructions.complementDivisorSupportedClass X R z) = 0 := by
  let f := Geometric.LocalHomology.Cycles.subspaceInclusion T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set T)
  let ha : Set.MapsTo f ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set T) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U))) (O : Set T) := fun _ hx => hx
  have hr : ∀ x, f x ∈ (Set.range (Supported.PrincipalDivisor.Constructions.complementDivisorSupport X R z).analyticInclusion)ᶜ := by
    intro x
    rw [(Supported.PrincipalDivisor.Constructions.complementDivisorSupport X R z).range_analyticInclusion]
    exact hU x.property
  have hz := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset (ModuleCat.of ℚ ℚ) f
    ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set T) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)))
    (Set.range (Supported.PrincipalDivisor.Constructions.complementDivisorSupport X R z).analyticInclusion)ᶜ
    (fun _ hx => Supported.PrincipalDivisor.Constructions.complementDivisorSupport_complement X R z (ha hx)) hr 2
  have hc : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T)
      (Supported.PrincipalDivisor.Constructions.complementDivisorSupport_complement X R z) 2 ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f ha 2 =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (fun _ hx => Supported.PrincipalDivisor.Constructions.complementDivisorSupport_complement X R z (ha hx)) 2 := by
    simpa only [Category.comp_id] using AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp
      (ModuleCat.of ℚ ℚ) f (𝟙 T) ha (Supported.PrincipalDivisor.Constructions.complementDivisorSupport_complement X R z) 2
  have hv := ConcreteCategory.congr_hom hc (Supported.PrincipalDivisor.Constructions.complementDivisorSupport X R z).rationalSupportedCycleClass
  rw [hz] at hv
  exact hv

local instance : Fintype (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R) := Fintype.ofFinite _

variable (g : X.carrier.functionField)

/-- The actual divisor sum has just its original coefficient in a
neighborhood isolating one reference divisor support. -/
theorem principalDivisorSupportedClass_restrict_isolated (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R))
    (U : X.carrier.Opens) (hU : U ≤ complementDivisorIsolatingOpen X R z) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
      (Supported.PrincipalDivisor.Constructions.principalDivisorSupportedClass X R g) =
      (X.carrier.ord g z.val : ℚ) •
        Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
          (Supported.PrincipalDivisor.Constructions.complementDivisorSupportedClass X R z) := by
  classical
  unfold Supported.PrincipalDivisor.Constructions.principalDivisorSupportedClass
  rw [map_sum, Finset.sum_eq_single z]
  · exact map_smul _ _ _
  · intro w _ hw
    rw [map_smul, complementDivisorSupportedClass_restrict_away X R w U
      (hU.trans (complementDivisorIsolatingOpen_subset_other_complement X R z w (Ne.symm hw))), smul_zero]
  · simp

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.DivisorIsolation
