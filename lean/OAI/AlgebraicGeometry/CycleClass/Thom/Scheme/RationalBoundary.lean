import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalUnitEvaluation
import OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization

/-! # Rational Boundary -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.LocalMultiplicity

/-! The actual local winding boundary of a rational function is its algebraic
integer exponent times the normalized relative class of its regular parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.Multiplicity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def lineMap {Y : TopCat.{0}} (h : C(Y, ℂ)) : Y ⟶ PrincipalBoundary.Constructions.normalComplexLine :=
  TopCat.ofHom ⟨fun y _ => h y, continuous_pi fun _ => h.continuous⟩

def puncturedLineMap {Y : TopCat.{0}} (h : C(Y, ℂ)) (hh : ∀ y, h y ≠ 0) :
    Y ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine :=
  TopCat.ofHom ⟨fun y => ⟨fun _ : Fin 1 => h y, fun hz => hh y (congrFun (Set.mem_singleton_iff.mp hz) 0)⟩,
    (continuous_pi fun _ => h.continuous).subtype_mk _⟩

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g) (U : X.left.Opens)

def rationalLocalBoundary : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) 2 :=
  WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary (TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U)
    (puncturedLineMap (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U))

theorem parameterMap_mapsTo (p : Γ(X.left, U))
    (hp : ∀ y : RationalUnitEvaluation.Constructions.referenceLocus X D U, SectionEvaluation.Constructions.sectionEvaluationOn X U p y.val ≠ 0) :
    Set.MapsTo (lineMap (Y := TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (SectionEvaluation.Constructions.sectionEvaluationOn X U p)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) PrincipalBoundary.Constructions.puncturedComplexLine := by
  intro y hy hz
  exact hp ⟨y, hy⟩ (congrFun (Set.mem_singleton_iff.mp hz) 0)

def parameterSupportedClass (p : Γ(X.left, U))
    (hp : ∀ y : RationalUnitEvaluation.Constructions.referenceLocus X D U, SectionEvaluation.Constructions.sectionEvaluationOn X U p y.val ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (lineMap (Y := TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (SectionEvaluation.Constructions.sectionEvaluationOn X U p))
    (parameterMap_mapsTo X D U p hp) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

theorem rationalLocalBoundary_power [Nonempty U]
    (p : Γ(X.left, U)) (hp : p ≠ 0) (v : Γ(X.left, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : g = X.left.germToFunctionField U v * (X.left.germToFunctionField U p) ^ m) :
    rationalLocalBoundary X D U = m • parameterSupportedClass X D U p
      (RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D U p v m he hp hm) := by
  let hp' := RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D U p v m he hp hm
  have h := WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary_unit_power (TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U)
    (Geometric.LocalHomology.Cycles.subspaceMap (lineMap (Y := TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (SectionEvaluation.Constructions.sectionEvaluationOn X U p)) (parameterMap_mapsTo X D U p hp'))
    (puncturedLineMap (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U))
    (SectionEvaluation.Constructions.sectionEvaluationOn X U (v : Γ(X.left, U))) (SectionEvaluation.Constructions.sectionEvaluationOn_unit_ne_zero X U v) m
    (by
      intro y
      change RationalUnitEvaluation.Constructions.referenceEquation X D U y = (SectionEvaluation.Constructions.sectionEvaluationOn X U p y.val) ^ m *
        SectionEvaluation.Constructions.sectionEvaluationOn X U (v : Γ(X.left, U)) y.val
      exact (RationalUnitEvaluation.Constructions.referenceEquation_power X D U p v m he y (hp' y)).trans (mul_comm _ _))
  rw [WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary_equation] at h
  exact h

theorem rationalLocalBoundary_algebraicOrder [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    (z : X.left) (hz : Order.coheight z = 1)
    (V : X.left.Opens) (hzV : z ∈ V) (hg : g ≠ 0) (hm : X.left.ord g z ≠ 0) :
    ∃ (U : X.left.Opens) (_ : U ∈ X.left.affineOpens) (hzU : z ∈ U) (_ : U ≤ V)
      (p : Γ(X.left, U)), Irreducible (X.left.presheaf.germ U z hzU p) ∧
      ∃ hp : ∀ y : RationalUnitEvaluation.Constructions.referenceLocus X D U, SectionEvaluation.Constructions.sectionEvaluationOn X U p y.val ≠ 0,
        rationalLocalBoundary X D U = (X.left.ord g z) • parameterSupportedClass X D U p hp := by
  obtain ⟨W, hW, hzW, hWV, p, v, hp, he⟩ :=
    HodgeConjecture.DegreeTwo.DivisorEquations.Constructions.smooth_rationalFunction_local_equation X.hom z hz V hzV g hg
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [h, map_zero]
  exact ⟨W, hW, hzW, hWV, p, hp,
    RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D W p v (X.left.ord g z) he hp0 hm,
    rationalLocalBoundary_power X D W p hp0 v (X.left.ord g z) hm he⟩

end AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.LocalMultiplicity

namespace AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.Restriction

/-! A single global connecting boundary for the rational function restricts
to the actual local boundary used in its algebraic multiplicity calculation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.LocalMultiplicity OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.Multiplicity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

def globalUnitMap : TopCat.of (SectionEvaluation.Constructions.analyticOpen X D.domain) ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine :=
  LocalMultiplicity.puncturedLineMap (SectionEvaluation.Constructions.sectionEvaluationOn X D.domain (D.unit : Γ(X.left, D.domain)))
    (SectionEvaluation.Constructions.sectionEvaluationOn_unit_ne_zero X D.domain D.unit)

def rationalGlobalBoundary : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) 2 :=
  WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (SectionEvaluation.Constructions.analyticOpen X D.domain) (globalUnitMap X D)

theorem rationalGlobalBoundary_absolute_zero :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SectionEvaluation.Constructions.analyticOpen X D.domain) 2 (rationalGlobalBoundary X D) = 0 :=
  WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary_absolute_zero _ _ _

variable (U : X.left.Opens)

def localAmbientMap : TopCat.of (SectionEvaluation.Constructions.analyticOpen X U) ⟶ TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (SectionEvaluation.Constructions.analyticOpen X U)

theorem localAmbientMap_mapsTo : Set.MapsTo (localAmbientMap X U) (RationalUnitEvaluation.Constructions.referenceLocus X D U)
    (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) := fun _ hx => hx

theorem referenceEquation_original (y : RationalUnitEvaluation.Constructions.referenceLocus X D U) :
    RationalUnitEvaluation.Constructions.referenceEquation X D U y = SectionEvaluation.Constructions.sectionEvaluationOn X D.domain (D.unit : Γ(X.left, D.domain))
      ⟨y.val.val, y.property⟩ := by
  exact SectionEvaluation.Constructions.sectionEvaluationOn_restrict X inf_le_right (D.unit : Γ(X.left, D.domain))
    (RationalUnitEvaluation.Constructions.referenceLocusIntersectionMap X D U y)

theorem localUnitMap_comp :
    Geometric.LocalHomology.Cycles.subspaceMap (localAmbientMap X U) (localAmbientMap_mapsTo X D U) ≫ globalUnitMap X D =
      LocalMultiplicity.puncturedLineMap (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U) := by
  ext y i
  change SectionEvaluation.Constructions.sectionEvaluationOn X D.domain (D.unit : Γ(X.left, D.domain)) ⟨y.val.val, y.property⟩ =
    RationalUnitEvaluation.Constructions.referenceEquation X D U y
  exact (referenceEquation_original X D U y).symm

theorem rationalGlobalBoundary_localRestriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (localAmbientMap X U)
      (localAmbientMap_mapsTo X D U) 2 (rationalGlobalBoundary X D) = LocalMultiplicity.rationalLocalBoundary X D U := by
  have hw := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceMap (localAmbientMap X U) (localAmbientMap_mapsTo X D U)) (globalUnitMap X D) 1) PrincipalBoundary.Constructions.lineWindingClass
  rw [localUnitMap_comp] at hw
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_naturality (ModuleCat.of ℚ ℚ)
      (localAmbientMap X U) (localAmbientMap_mapsTo X D U) 1)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (globalUnitMap X D) 1 PrincipalBoundary.Constructions.lineWindingClass)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (localAmbientMap X U)
      (localAmbientMap_mapsTo X D U) 2 (rationalGlobalBoundary X D) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) (TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceMap (localAmbientMap X U) (localAmbientMap_mapsTo X D U)) 1
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (globalUnitMap X D) 1 PrincipalBoundary.Constructions.lineWindingClass)) at h
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (LocalMultiplicity.puncturedLineMap (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U)) 1 PrincipalBoundary.Constructions.lineWindingClass =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceMap (localAmbientMap X U) (localAmbientMap_mapsTo X D U)) 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (globalUnitMap X D) 1 PrincipalBoundary.Constructions.lineWindingClass) at hw
  rw [← hw] at h
  exact h

end AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.Restriction

namespace AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.Unit

/-! The actual rational-function boundary vanishes on neighborhoods where
the function is an algebraic unit, including every codimension-one point of order zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalUnitEvaluation.Constructions
  LocalMultiplicity WindingNormalization.Constructions.Multiplicity Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem normalizedWindingBoundary_extending {X : TopCat.{0}} (A : Set X)
    (f : X ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) :
    WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary X A (Geometric.LocalHomology.Cycles.subspaceInclusion X A ≫ f) = 0 := by
  unfold WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp]
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction_connecting (ModuleCat.of ℚ ℚ) X A 1)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 PrincipalBoundary.Constructions.lineWindingClass)

theorem normalizedWindingBoundary_extending_unit {X : TopCat.{0}} (A : Set X)
    (u : C(X, ℂ)) (hu : ∀ x, u x ≠ 0) :
    WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary X A
      (LocalMultiplicity.puncturedLineMap (u.comp ⟨Subtype.val, continuous_subtype_val⟩) (fun x => hu x.val)) = 0 := by
  have h : Geometric.LocalHomology.Cycles.subspaceInclusion X A ≫ LocalMultiplicity.puncturedLineMap u hu =
      LocalMultiplicity.puncturedLineMap (Y := TopCat.of A)
        (u.comp ⟨Subtype.val, continuous_subtype_val⟩) (fun x => hu x.val) := by
    ext x i
    rfl
  exact h ▸ normalizedWindingBoundary_extending A (LocalMultiplicity.puncturedLineMap u hu)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)
  (U : X.left.Opens) [Nonempty U]

theorem referenceEquation_unit (v : Γ(X.left, U)ˣ) (he : g = X.left.germToFunctionField U v)
    (y : RationalUnitEvaluation.Constructions.referenceLocus X D U) :
    RationalUnitEvaluation.Constructions.referenceEquation X D U y = SectionEvaluation.Constructions.sectionEvaluationOn X U (v : Γ(X.left, U)) y.val := by
  let W := U ⊓ D.domain
  let z := RationalUnitEvaluation.Constructions.referenceLocusIntersectionMap X D U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  have ht : X.left.presheaf.map (homOfLE (show W ≤ D.domain from inf_le_right)).op
      (D.unit : Γ(X.left, D.domain)) =
      X.left.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op (v : Γ(X.left, U)) := by
    apply X.left.germToFunctionField_injective W
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, D.represents]
    exact he
  change SectionEvaluation.Constructions.sectionEvaluationOn X W
    (X.left.presheaf.map (homOfLE inf_le_right).op (D.unit : Γ(X.left, D.domain))) z = _
  rw [ht, SectionEvaluation.Constructions.sectionEvaluationOn_restrict]
  rfl

theorem rationalLocalBoundary_unit (v : Γ(X.left, U)ˣ) (he : g = X.left.germToFunctionField U v) :
    LocalMultiplicity.rationalLocalBoundary X D U = 0 := by
  let u : C(TopCat.of (SectionEvaluation.Constructions.analyticOpen X U), ℂ) := SectionEvaluation.Constructions.sectionEvaluationOn X U (v : Γ(X.left, U))
  have hu : ∀ x, u x ≠ 0 := SectionEvaluation.Constructions.sectionEvaluationOn_unit_ne_zero X U v
  have hm : LocalMultiplicity.puncturedLineMap (Y := TopCat.of (RationalUnitEvaluation.Constructions.referenceLocus X D U))
      (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U) =
      LocalMultiplicity.puncturedLineMap (Y := TopCat.of (RationalUnitEvaluation.Constructions.referenceLocus X D U))
        (u.comp ⟨Subtype.val, continuous_subtype_val⟩) (fun x => hu x.val) := by
    ext y i
    exact referenceEquation_unit X D U v he y
  unfold LocalMultiplicity.rationalLocalBoundary
  rw [hm]
  exact normalizedWindingBoundary_extending_unit (X := TopCat.of (SectionEvaluation.Constructions.analyticOpen X U))
    (RationalUnitEvaluation.Constructions.referenceLocus X D U) u hu

omit [Nonempty U] in
theorem rationalGlobalBoundary_local_zero_of_order_zero [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    (z : X.left) (hz : Order.coheight z = 1)
    (V : X.left.Opens) (hzV : z ∈ V) (hg : g ≠ 0) (hm : X.left.ord g z = 0) :
    ∃ (W : X.left.Opens) (_ : W ∈ X.left.affineOpens) (_ : z ∈ W) (_ : W ≤ V),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Restriction.localAmbientMap X W)
        (Restriction.localAmbientMap_mapsTo X D W) 2 (Restriction.rationalGlobalBoundary X D) = 0 := by
  obtain ⟨W, hW, hzW, hWV, p, v, _, he⟩ :=
    HodgeConjecture.DegreeTwo.DivisorEquations.Constructions.smooth_rationalFunction_local_equation X.hom z hz V hzV g hg
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  rw [hm, zpow_zero, mul_one] at he
  refine ⟨W, hW, hzW, hWV, ?_⟩
  rw [Restriction.rationalGlobalBoundary_localRestriction]
  exact rationalLocalBoundary_unit X D W v he

end AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.Unit

end

end OAI
