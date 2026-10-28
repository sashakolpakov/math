import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionImmersionPair
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.ClosedEquationQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Principal Immersion Pair -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalImmersionPair.BundleCycles

noncomputable section

section

/-! Normal coordinates for a global section are constructed from the literal principal kernel of its smooth closed zero scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

variable {Y X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral X.left] [Smooth X.hom] (i : Y ⟶ X) [IsClosedImmersion i.left]
  (s : Γ(X.left, ⊤)) (hs : s ≠ 0)
  (hzero : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) = Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s))
  (hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom + 1 =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)

include hs hzero hd in
theorem schemePrincipalImmersion_exists_normalPair
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (U : X.left.Opens) (hU : IsAffineOpen U)
    (hxU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X U)
    (hk : RingHom.ker (i.left.app U).hom =
      Ideal.span {X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s}) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
        (Fin 1 → ℂ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) x,
      P.ambientChart.MDifferentiable
        𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
        𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin 1 → ℂ)) ∧
      ∀ y : P.neighborhood, P.normalCoordinate y = CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s y.val := by
  let : Nonempty U := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x), hxU⟩⟩
  let sU := X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s
  have hsU : sU ≠ 0 := (map_ne_zero_iff _
    (map_injective_of_isIntegral X.left (homOfLE (show U ≤ ⊤ from le_top)))).mpr hs
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
  let : Algebra.Smooth ℂ (Γ(X.left, U) ⧸ Ideal.span {sU}) := LineBundles.Smooth.ClosedEquationQuotient.BundleCycles.smoothClosedEquation_quotient i U hU sU hk
  let Q := Γ(X.left, U) ⧸ Ideal.span {sU}
  let a : Q := Ideal.Quotient.mk (Ideal.span {sU}) (1 : Γ(X.left, U))
  let : Algebra.Smooth Q (Localization.Away a) := Algebra.Smooth.of_isLocalization_Away a
  have hsm : Algebra.Smooth ℂ (Localization.Away a) := Algebra.Smooth.comp ℂ Q (Localization.Away a)
  have hb : CycleClass.Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X U (1 : Γ(X.left, U)) ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x, hxU⟩ ≠ 0 :=
    CycleClass.Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn_unit_ne_zero X U 1 ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x, hxU⟩
  exact SectionImmersionPair.BundleCycles.schemeSectionImmersion_exists_normalPair i s hzero hd x U hU hxU hsU 1 hsm hb

end

/-! The global section class is the actual Thom class of its smooth closed zero scheme. The equation charts are constructed from its principal kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

variable {Y X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (i : Y ⟶ X) [IsClosedImmersion i.left] (s : Γ(X.left, ⊤))
  (hzero : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) = Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s))

include hzero in
omit [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsClosedImmersion (Over.Hom.left i)] in
theorem schemePrincipalImmersion_equation_mapsTo : Set.MapsTo (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s)
    (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i))ᶜ Principal.Boundary.BundleCycles.puncturedComplexLine := by
  intro x hx
  apply CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo X s
  rwa [← hzero]

include hzero in
omit [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsClosedImmersion (Over.Hom.left i)] in
theorem schemePrincipalImmersion_section_mapsTo : Set.MapsTo (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i))ᶜ (Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s))ᶜ := by
  intro x hx
  rwa [← hzero]

variable (hs : s ≠ 0)
  (hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom + 1 =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
  (hlocal : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y, ∃ (U : X.left.Opens), IsAffineOpen U ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X U ∧
    RingHom.ker (i.left.app U).hom =
      Ideal.span {X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s})

include hs hlocal in
theorem schemePrincipalImmersion_equationClass_eq_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s)
      (schemePrincipalImmersion_equation_mapsTo i s hzero) 2 (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) =
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hd).regularThomClass := by
  classical
  choose U hU hxU hk using hlocal
  have he := fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y =>
    schemePrincipalImmersion_exists_normalPair i s hs hzero hd x (U x) (hU x) (hxU x) (hk x)
  choose P hP hcoord using he
  let Z := CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hd
  apply CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree_unique Z.regularComplementInclusion Z.holomorphic
    Z.differential_injective Z.closed 1 Z.regularComplement_complexImmersionCodimension P hP
  intro x
  rw [(P x).rationalClassFin_eq_normalPullback]
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (P x).neighborhood
  have hj : Set.MapsTo j (P x).relativeComplement (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i))ᶜ := fun _ hx => hx
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s)
    hj (schemePrincipalImmersion_equation_mapsTo i s hzero) 2
  have hmap : j ≫ CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s = (P x).normalCoordinate := by
    ext y a
    exact congrFun (hcoord x y).symm a
  have hm := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr hmap
    ((schemePrincipalImmersion_equation_mapsTo i s hzero).comp hj) (P x).normalCoordinate_mapsTo 2
  exact ConcreteCategory.congr_hom (hc.trans hm) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

include hs hlocal in
theorem schemePrincipalImmersion_sectionClass_eq_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (schemePrincipalImmersion_section_mapsTo i s hzero) 2 (Finite.GlobalSectionClassRestriction.BundleCycles.schemeSectionSupportedClass X s) =
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hd).regularThomClass := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s)
    (schemePrincipalImmersion_section_mapsTo i s hzero) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo X s) 2
  have he := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
    (Category.id_comp (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s))
    ((CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo X s).comp (schemePrincipalImmersion_section_mapsTo i s hzero))
    (schemePrincipalImmersion_equation_mapsTo i s hzero) 2
  exact (ConcreteCategory.congr_hom (h.trans he) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)).trans
    (schemePrincipalImmersion_equationClass_eq_Thom i s hzero hs hd hlocal)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalImmersionPair.BundleCycles
