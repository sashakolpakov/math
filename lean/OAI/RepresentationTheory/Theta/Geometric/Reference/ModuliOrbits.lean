import OAI.RepresentationTheory.Theta.Geometric.Reference.PELKernel
import OAI.RepresentationTheory.Theta.Geometric.EmbeddingSpan
import OAI.RepresentationTheory.Theta.Geometric.Finite.IntegralModuli

/-! # Moduli Orbits -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The fibers of the actual reference moduli map are exactly the
original rational SU orbits with the full specified finite marking. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry}

section

variable {x y : D.domain} (R : D.ReferencePELPointData hg x) (S : D.ReferencePELPointData hg y)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.rationalMatrix_point (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family S.family) :
    y.val = D.periodMap (R.rationalMatrix S e) x.val :=
  D.periodPoint_of_kernel hg (R.rationalMatrix S e) x y (R.rationalMatrix_kernel S e)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.finite_orbit_of_point_eq (hc : D.HasFiniteCoordinates) (h : R.point = S.point) :
    ∃ g : D.RationalSU,
      D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup ∧
        y.val = D.periodMap g x.val := by
  obtain ⟨e⟩ := R.familyIso_of_point_eq S h
  exact ⟨R.rationalMatrix S e, R.rationalMatrix_finite S e hc, R.rationalMatrix_point S e⟩

end

variable (D hg) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

include hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.referenceModuliMap_orbits (x y : D.domain) :
    D.referenceModuliMap hg x = D.referenceModuliMap hg y ↔
      ∃ g : D.RationalSU,
        D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup ∧
          y.val = D.periodMap g x.val := by
  constructor
  · exact (D.referencePELPointData hg x).finite_orbit_of_point_eq
      (D.referencePELPointData hg y) hc
  · rintro ⟨g, hf, hy⟩
    have he : y = D.rationalPeriodPoint g x := Subtype.ext hy
    rw [he]
    exact D.referenceModuliMap_finiteIntegral hg hc hgood hdegree g hf x

end

/-! Integral rational transport retains its exact action on the native
rational marking in the resulting full PEL isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} (g : D.RationalSU)
    (hΛ : ∀ v, v ∈ D.pel.reference.lattice ↔ D.rationalLinear g v ∈ D.pel.reference.lattice)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hc : D.HasFiniteCoordinates)
    (haway : D.away g ∈ D.awayLevel) (x : D.domain)
    (R : D.ReferencePELPointData hg x) (S : D.ReferencePELPointData hg (D.rationalPeriodPoint g x))

include hΛ hgood hc haway in
theorem Data.ActiveHeckeThetaData.integralRational_markedFamilyIso :
    ∃ e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family S.family,
      letI : IsMonHom (e.abelian.hom : R.model.abelian.toOver ⟶ S.model.abelian.toOver) := e.abelianGroup
      ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.abelian.hom ((R.model.toNativeReferenceModel R.analytic).nativeReferenceMarking v) =
          (S.model.toNativeReferenceModel S.analytic).nativeReferenceMarking (D.rationalLinear g v) := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  obtain ⟨e, he, hp⟩ := D.exists_integralRationalPeriodIso hg g hΛ x R.model S.model
  let : IsMonHom e.hom := he
  have hv (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (R.model.period (QuotientAddGroup.mk v)) =
        S.model.period (QuotientAddGroup.mk (D.rationalPeriodLinear g x v)) := hp _
  have hr (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := Data.ActiveHeckeThetaData.rationalReference_rationalPeriods hg g x
    R.analytic S.analytic R.model S.model e.hom hv v
  refine ⟨R.polarization.pelFamilyIso_of_chern_isometry S.polarization e D.pel.level ?_ ?_ ?_, hr⟩
  · exact Reference.MarkedChernIsometry.reference_marked_chern_isometry R.polarization S.polarization e.hom
      (D.rationalLinear g) (D.rationalLinear_traceForm g) hr
  · intro a
    change AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.model.abelian.toOver (R.model.action a) ≫ e.hom =
      e.hom ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap S.model.abelian.toOver (S.model.action a)
    exact D.integralRational_action hg g hΛ x R.model S.model e.hom hp a
  · intro T c
    change ((R.model.fixedReferenceLevel R.analytic).hom.app (.op T) c).val ≫ e.hom =
      ((S.model.fixedReferenceLevel S.analytic).hom.app (.op T) c).val
    exact D.integralRational_level hg g hΛ x R.model S.model e.hom hp
      R.analytic S.analytic hgood hc haway T c

include hΛ hgood hc haway in
theorem Data.ActiveHeckeThetaData.integralRational_markedFamilyIso_to {y : D.domain}
    (T : D.ReferencePELPointData hg y) (hy : y = D.rationalPeriodPoint g x) :
    ∃ e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family T.family,
      letI : IsMonHom (e.abelian.hom : R.model.abelian.toOver ⟶ T.model.abelian.toOver) := e.abelianGroup
      ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.abelian.hom ((R.model.toNativeReferenceModel R.analytic).nativeReferenceMarking v) =
          (T.model.toNativeReferenceModel T.analytic).nativeReferenceMarking (D.rationalLinear g v) := by
  subst y
  exact Data.ActiveHeckeThetaData.integralRational_markedFamilyIso g hΛ hgood hc haway x R T

end

end OAI.RepresentationTheory.Theta.Geometric
