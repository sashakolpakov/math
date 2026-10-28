import OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation
import OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization

/-! # Rational Boundary -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.LocalMultiplicity

/-! The actual local winding boundary of a rational function is its algebraic
integer exponent times the normalized relative class of its regular parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.Multiplicity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def lineMap {Y : TopCat.{0}} (h : C(Y, ℂ)) : Y ⟶ PrincipalBoundary.Constructions.normalComplexLine :=
  TopCat.ofHom ⟨fun y _ => h y, continuous_pi fun _ => h.continuous⟩

def puncturedLineMap {Y : TopCat.{0}} (h : C(Y, ℂ)) (hh : ∀ y, h y ≠ 0) :
    Y ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine :=
  TopCat.ofHom ⟨fun y => ⟨fun _ : Fin 1 => h y, fun hz => hh y (congrFun (Set.mem_singleton_iff.mp hz) 0)⟩,
    (continuous_pi fun _ => h.continuous).subtype_mk _⟩

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  {g : X.carrier.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.carrier g) (U : X.carrier.Opens)

def rationalLocalBoundary : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) 2 :=
  WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U)
    (puncturedLineMap (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U))

theorem parameterMap_mapsTo (p : Γ(X.carrier, U))
    (hp : ∀ y : RationalUnitEvaluation.Constructions.referenceLocus X D U, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0) :
    Set.MapsTo (lineMap (Y := TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) PrincipalBoundary.Constructions.puncturedComplexLine := by
  intro y hy hz
  exact hp ⟨y, hy⟩ (congrFun (Set.mem_singleton_iff.mp hz) 0)

def parameterSupportedClass (p : Γ(X.carrier, U))
    (hp : ∀ y : RationalUnitEvaluation.Constructions.referenceLocus X D U, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (lineMap (Y := TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p))
    (parameterMap_mapsTo X D U p hp) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

theorem rationalLocalBoundary_power [Nonempty U]
    (p : Γ(X.carrier, U)) (hp : p ≠ 0) (v : Γ(X.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : g = X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m) :
    rationalLocalBoundary X D U = m • parameterSupportedClass X D U p
      (RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D U p v m he hp hm) := by
  let hp' := RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D U p v m he hp hm
  have h := WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary_unit_power (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U)
    (Geometric.LocalHomology.Cycles.subspaceMap (lineMap (Y := TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p)) (parameterMap_mapsTo X D U p hp'))
    (puncturedLineMap (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U))
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U))) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X U v) m
    (by
      intro y
      change RationalUnitEvaluation.Constructions.referenceEquation X D U y = (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val) ^ m *
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U)) y.val
      exact (RationalUnitEvaluation.Constructions.referenceEquation_power X D U p v m he y (hp' y)).trans (mul_comm _ _))
  rw [WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary_equation] at h
  exact h

theorem rationalLocalBoundary_algebraicOrder (z : X.carrier) (hz : Order.coheight z = 1)
    (V : X.carrier.Opens) (hzV : z ∈ V) (hg : g ≠ 0) (hm : X.carrier.ord g z ≠ 0) :
    ∃ (U : X.carrier.Opens) (_ : U ∈ X.carrier.affineOpens) (hzU : z ∈ U) (_ : U ≤ V)
      (p : Γ(X.carrier, U)), Irreducible (X.carrier.presheaf.germ U z hzU p) ∧
      ∃ hp : ∀ y : RationalUnitEvaluation.Constructions.referenceLocus X D U, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0,
        rationalLocalBoundary X D U = (X.carrier.ord g z) • parameterSupportedClass X D U p hp := by
  let : Smooth X.structureMap := X.smooth
  obtain ⟨W, hW, hzW, hWV, p, v, hp, he⟩ :=
    HodgeConjecture.DegreeTwo.DivisorEquations.Constructions.smooth_rationalFunction_local_equation X.structureMap z hz V hzV g hg
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [h, map_zero]
  exact ⟨W, hW, hzW, hWV, p, hp,
    RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D W p v (X.carrier.ord g z) he hp0 hm,
    rationalLocalBoundary_power X D W p hp0 v (X.carrier.ord g z) hm he⟩

end AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.LocalMultiplicity

namespace AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.Restriction

/-! A single global connecting boundary for the rational function restricts
to the actual local boundary used in its algebraic multiplicity calculation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.LocalMultiplicity OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.Multiplicity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  {g : X.carrier.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.carrier g)

def globalUnitMap : TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain) ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine :=
  LocalMultiplicity.puncturedLineMap (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X D.domain (D.unit : Γ(X.carrier, D.domain)))
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X D.domain D.unit)

def rationalGlobalBoundary : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain : Set (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) 2 :=
  WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain) (globalUnitMap X D)

theorem rationalGlobalBoundary_absolute_zero :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain) 2 (rationalGlobalBoundary X D) = 0 :=
  WindingNormalization.Constructions.Multiplicity.normalizedWindingBoundary_absolute_zero _ _ _

variable (U : X.carrier.Opens)

def localAmbientMap : TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) ⟶ TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)

theorem localAmbientMap_mapsTo : Set.MapsTo (localAmbientMap X U) (RationalUnitEvaluation.Constructions.referenceLocus X D U)
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain : Set (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) := fun _ hx => hx

theorem referenceEquation_original (y : RationalUnitEvaluation.Constructions.referenceLocus X D U) :
    RationalUnitEvaluation.Constructions.referenceEquation X D U y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X D.domain (D.unit : Γ(X.carrier, D.domain))
      ⟨y.val.val, y.property⟩ := by
  exact DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict X inf_le_right (D.unit : Γ(X.carrier, D.domain))
    (RationalUnitEvaluation.Constructions.referenceLocusIntersectionMap X D U y)

theorem localUnitMap_comp :
    Geometric.LocalHomology.Cycles.subspaceMap (localAmbientMap X U) (localAmbientMap_mapsTo X D U) ≫ globalUnitMap X D =
      LocalMultiplicity.puncturedLineMap (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U) := by
  ext y i
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X D.domain (D.unit : Γ(X.carrier, D.domain)) ⟨y.val.val, y.property⟩ =
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
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (RationalUnitEvaluation.Constructions.referenceLocus X D U) 1
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

end AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.Restriction

namespace AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.Unit

/-! The actual rational-function boundary vanishes on neighborhoods where
the function is an algebraic unit, including every codimension-one point of order zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation.Constructions
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

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  {g : X.carrier.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.carrier g)
  (U : X.carrier.Opens) [Nonempty U]

theorem referenceEquation_unit (v : Γ(X.carrier, U)ˣ) (he : g = X.carrier.germToFunctionField U v)
    (y : RationalUnitEvaluation.Constructions.referenceLocus X D U) :
    RationalUnitEvaluation.Constructions.referenceEquation X D U y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U)) y.val := by
  let W := U ⊓ D.domain
  let z := RationalUnitEvaluation.Constructions.referenceLocusIntersectionMap X D U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  have ht : X.carrier.presheaf.map (homOfLE (show W ≤ D.domain from inf_le_right)).op
      (D.unit : Γ(X.carrier, D.domain)) =
      X.carrier.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op (v : Γ(X.carrier, U)) := by
    apply X.carrier.germToFunctionField_injective W
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, D.represents]
    exact he
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W
    (X.carrier.presheaf.map (homOfLE inf_le_right).op (D.unit : Γ(X.carrier, D.domain))) z = _
  rw [ht, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict]
  rfl

theorem rationalLocalBoundary_unit (v : Γ(X.carrier, U)ˣ) (he : g = X.carrier.germToFunctionField U v) :
    LocalMultiplicity.rationalLocalBoundary X D U = 0 := by
  let u : C(TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U), ℂ) := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U))
  have hu : ∀ x, u x ≠ 0 := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X U v
  have hm : LocalMultiplicity.puncturedLineMap (Y := TopCat.of (RationalUnitEvaluation.Constructions.referenceLocus X D U))
      (RationalUnitEvaluation.Constructions.referenceEquation X D U) (RationalUnitEvaluation.Constructions.referenceEquation_ne_zero X D U) =
      LocalMultiplicity.puncturedLineMap (Y := TopCat.of (RationalUnitEvaluation.Constructions.referenceLocus X D U))
        (u.comp ⟨Subtype.val, continuous_subtype_val⟩) (fun x => hu x.val) := by
    ext y i
    exact referenceEquation_unit X D U v he y
  unfold LocalMultiplicity.rationalLocalBoundary
  rw [hm]
  exact normalizedWindingBoundary_extending_unit (X := TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U))
    (RationalUnitEvaluation.Constructions.referenceLocus X D U) u hu

omit [Nonempty U] in
theorem rationalGlobalBoundary_local_zero_of_order_zero (z : X.carrier) (hz : Order.coheight z = 1)
    (V : X.carrier.Opens) (hzV : z ∈ V) (hg : g ≠ 0) (hm : X.carrier.ord g z = 0) :
    ∃ (W : X.carrier.Opens) (_ : W ∈ X.carrier.affineOpens) (_ : z ∈ W) (_ : W ≤ V),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Restriction.localAmbientMap X W)
        (Restriction.localAmbientMap_mapsTo X D W) 2 (Restriction.rationalGlobalBoundary X D) = 0 := by
  let : Smooth X.structureMap := X.smooth
  obtain ⟨W, hW, hzW, hWV, p, v, _, he⟩ :=
    HodgeConjecture.DegreeTwo.DivisorEquations.Constructions.smooth_rationalFunction_local_equation X.structureMap z hz V hzV g hg
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  rw [hm, zpow_zero, mul_one] at he
  refine ⟨W, hW, hzW, hWV, ?_⟩
  rw [Restriction.rationalGlobalBoundary_localRestriction]
  exact rationalLocalBoundary_unit X D W v he

end AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.Unit

end

end OAI
