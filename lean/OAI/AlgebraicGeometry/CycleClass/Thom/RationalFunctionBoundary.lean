import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalBoundary
import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Rational Function Boundary -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal

noncomputable section

/-!
# ThomClass: the boundary class of an actual rational function

Every nonzero rational function on an integral scheme is an algebraic unit
on a nonempty open. Its actual complex-point evaluation gives a winding
class on that analytic open, and the connecting homomorphism gives a
relative class on the ambient complex-point space. Its absolute image is
proved to be zero.

The local comparison of this relative boundary with the divisor's
fundamental-cycle multiplicities is still required. No assertion of that
comparison is included in the representative data.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

section

/-- Actual unit data representing a rational function on a nonempty open. -/
structure RationalUnitRepresentative (X : Scheme) [IsIntegral X]
    (f : X.functionField) where
  domain : X.Opens
  nonempty_domain : Nonempty domain
  unit : Γ(X, domain)ˣ
  represents : letI := nonempty_domain
    X.germToFunctionField domain (unit : Γ(X, domain)) = f

/-- Existence is supplied by the function-field construction, with no
cohomological hypotheses. -/
def rationalUnitRepresentative (X : Scheme) [IsIntegral X]
    (f : X.functionField) (hf : f ≠ 0) : RationalUnitRepresentative X f := by
  apply Classical.choice
  obtain ⟨U, _, a, hU, hfa, ha⟩ := exists_isUnit_germ_eq X f hf
  refine ⟨⟨U, hU, ha.unit, ?_⟩⟩
  simpa only [ha.unit_spec] using hfa

namespace RationalUnitRepresentative

variable {X : Scheme} [IsIntegral X] {f : X.functionField}

instance (D : RationalUnitRepresentative X f) : Nonempty D.domain := D.nonempty_domain

/-- The divisor coefficients vanish on every such unit-representing open. -/
theorem ord_eq_zero (D : RationalUnitRepresentative X f)
    [IsLocallyNoetherian X] (x : X) (hx : x ∈ D.domain) : X.ord f x = 0 := by
  rw [← D.represents]
  exact Scheme.ord_of_isUnit D.unit.isUnit hx

/-- Restriction of a regular section leaves its function-field germ unchanged. -/
theorem germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op a) =
      X.germToFunctionField U a :=
  X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) _ a

/-- Any two representatives of the same rational function agree on every
common nonempty subopen, by injectivity into the actual function field. -/
theorem agree_on_common_open (D E : RationalUnitRepresentative X f)
    (V : X.Opens) [Nonempty V] (hD : V ≤ D.domain) (hE : V ≤ E.domain) :
    X.presheaf.map (homOfLE hD).op (D.unit : Γ(X, D.domain)) =
      X.presheaf.map (homOfLE hE).op (E.unit : Γ(X, E.domain)) := by
  apply X.germToFunctionField_injective V
  rw [germ_restrict, germ_restrict, D.represents, E.represents]

/-- The unit open, with the inherited complex scheme structure. -/
def domainOver (D : RationalUnitRepresentative X f) (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (D.domain.ι ≫ s)

/-- Its actual open inclusion as a morphism over the complex base. -/
def domainInclusion (D : RationalUnitRepresentative X f) (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    D.domainOver s ⟶ Over.mk s := Over.homMk D.domain.ι rfl

instance domainInclusion_isOpenImmersion (D : RationalUnitRepresentative X f)
    (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) : IsOpenImmersion (D.domainInclusion s).left := by
  change IsOpenImmersion D.domain.ι
  infer_instance

/-- The analytic open in the ambient complex-point space. -/
def analyticDomain (D : RationalUnitRepresentative X f) (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Set (Betti.Scheme.schemePointSpace (Over.mk s)) :=
  Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (D.domainInclusion s))

theorem analyticDomain_isOpen (D : RationalUnitRepresentative X f)
    (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) : IsOpen (D.analyticDomain s) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion
    (D.domainInclusion s)).isOpen_range

/-- The analytic open is identified with the points of the actual open subscheme. -/
def analyticDomainHomeomorph (D : RationalUnitRepresentative X f)
    (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.domainOver s) ≃ₜ D.analyticDomain s :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion
    (D.domainInclusion s)).isEmbedding.toHomeomorph

/-- Transfer the unit to global sections of the open subscheme. -/
def unitOnOpenScheme (D : RationalUnitRepresentative X f) :
    Γ(D.domain.toScheme, ⊤)ˣ :=
  Units.map D.domain.topIso.inv.hom.toMonoidHom D.unit

/-- Evaluation of the rational function on its actual analytic unit domain. -/
def analyticUnitMap (D : RationalUnitRepresentative X f) (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    TopCat.of (D.analyticDomain s) ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine := by
  let F : C(D.analyticDomain s, ℂ) :=
    (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionContinuousMap (D.domainOver s)
      (D.unitOnOpenScheme : Γ(D.domain.toScheme, ⊤))).comp
      ⟨(D.analyticDomainHomeomorph s).symm, (D.analyticDomainHomeomorph s).symm.continuous⟩
  have hF (x : D.analyticDomain s) : F x ≠ 0 := by
    exact DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_unit_ne_zero
      (X := D.domainOver s) D.unitOnOpenScheme ((D.analyticDomainHomeomorph s).symm x)
  refine TopCat.ofHom ⟨fun x => ⟨(fun _ : Fin 1 => F x), ?_⟩, ?_⟩
  · change (fun _ : Fin 1 => F x) ≠ 0
    intro h
    exact hF x (congrFun h 0)
  · exact (continuous_pi fun _ => F.continuous).subtype_mk _

/-- The winding class of the nonzero rational function on the analytic open. -/
def windingClass (D : RationalUnitRepresentative X f) (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (D.analyticDomain s)) 1 :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (D.analyticUnitMap s) 1 PrincipalBoundary.Constructions.lineWindingClass

/-- The relative divisor-boundary class attached to the genuine rational function. -/
def supportedBoundary (D : RationalUnitRepresentative X f) (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace (Over.mk s))
      (D.analyticDomain s) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace (Over.mk s))
    (D.analyticDomain s) 1 (D.windingClass s)

/-- This boundary has zero image in the actual ordinary cohomology of X(ℂ). -/
theorem supportedBoundary_absolute_zero (D : RationalUnitRepresentative X f)
    (s : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace (Over.mk s))
      (D.analyticDomain s) 2 (D.supportedBoundary s) = 0 :=
  ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_inclusion (ModuleCat.of ℚ ℚ)
      (Betti.Scheme.schemePointSpace (Over.mk s)) (D.analyticDomain s) 1) (D.windingClass s)

end RationalUnitRepresentative

end

/-- The literal ThomClass coefficient vanishes wherever the actual rational function
is represented by an algebraic unit. -/
theorem principalDivisorCoefficient_unitDomain (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : TopologicalSpace.IrreducibleCloseds X.carrier)
    (f : (Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (D : RationalUnitRepresentative (Geometric.GenericPoint.reducedSupportScheme W) f)
    (C : TopologicalSpace.IrreducibleCloseds X.carrier) (y : Geometric.GenericPoint.reducedSupportScheme W)
    (hy : Geometric.GenericPoint.reducedSupportι W y = IntersectionGeometry.supportPoint C) (hU : y ∈ D.domain) :
    IntersectionGeometry.principalDivisorCoefficient X W f C = 0 := by
  rw [IntersectionGeometry.principalDivisorCoefficient_at_image X W f C y hy, D.ord_eq_zero y hU]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal
