import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain
import OAI.RepresentationTheory.Theta.Geometric.Period.Ne

/-! # Period Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodAction.Multiplicity

noncomputable section

/-! The actual rational special-unitary action on the signed native
period domain, with its continuous fractional-linear coordinate map. -/

open OAI.RepresentationTheory.Theta.Geometric.Period.Ne

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

theorem native_periodMap_preserves (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) : RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z ∈ P.domain := by
  rw [PeriodDomain.Multiplicity.native_domain_eq_ball E P] at hz ⊢
  exact RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_preserves P.b P.μ g z hz

@[instance_reducible] def nativeDomainAction : MulAction (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} where
  smul g z := ⟨RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z, native_periodMap_preserves E P g z z.property⟩
  one_smul z := by
    apply Subtype.ext
    change RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ 1 z.val = z.val
    rw [map_one]
    rfl
  mul_smul g h z := by
    apply Subtype.ext
    change RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ (g * h) z.val =
      RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ h z.val)
    rw [map_mul]
    rfl

attribute [local instance] nativeDomainAction

theorem nativeDomain_smul_val (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (g • z).val = RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z := rfl

theorem nativeDomain_smul_continuous (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    Continuous (fun z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} => g • z) := by
  apply Continuous.subtype_mk
  have h := (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_differentiableOn P.b P.μ g).continuousOn
  rw [← PeriodDomain.Multiplicity.native_domain_eq_ball E P] at h
  exact continuousOn_iff_continuous_domRestrict.mp h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodAction.Multiplicity
