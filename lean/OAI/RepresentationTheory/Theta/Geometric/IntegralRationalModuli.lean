import OAI.RepresentationTheory.Theta.Geometric.Rational.ClearedPeriods
import OAI.RepresentationTheory.Theta.Geometric.IntegralRationalCompatibility
import OAI.RepresentationTheory.Theta.Geometric.Reference.MarkedChernIsometry
import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliPoints
import OAI.RepresentationTheory.Theta.Geometric.Rational.Polarization

/-! # Integral Rational Moduli -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual reference moduli point is invariant under rational SU
maps preserving the original lattice and original ordered away level. -/

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

include hΛ hgood hc haway

theorem Data.ActiveHeckeThetaData.integralRational_familyIso : Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family S.family) := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  obtain ⟨e, he, hp⟩ := D.exists_integralRationalPeriodIso hg g hΛ x R.model S.model
  let : IsMonHom e.hom := he
  have hv (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (R.model.period (QuotientAddGroup.mk v)) =
        S.model.period (QuotientAddGroup.mk (D.rationalPeriodLinear g x v)) := hp _
  have hr (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := Data.ActiveHeckeThetaData.rationalReference_rationalPeriods hg g x
    R.analytic S.analytic R.model S.model e.hom hv v
  refine ⟨R.polarization.pelFamilyIso_of_chern_isometry S.polarization e D.pel.level ?_ ?_ ?_⟩
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

theorem Data.ActiveHeckeThetaData.integralRational_point_eq : R.point = S.point := by
  apply S.point_unique
  exact ⟨R.point_family.some.trans (Data.ActiveHeckeThetaData.integralRational_familyIso g hΛ hgood hc haway x R S).some⟩

theorem Data.ActiveHeckeThetaData.referenceModuliMap_integralRational :
    D.referenceModuliMap hg x = D.referenceModuliMap hg (D.rationalPeriodPoint g x) :=
  Data.ActiveHeckeThetaData.integralRational_point_eq g hΛ hgood hc haway x
    (D.referencePELPointData hg x) (D.referencePELPointData hg (D.rationalPeriodPoint g x))

end

end OAI.RepresentationTheory.Theta.Geometric
