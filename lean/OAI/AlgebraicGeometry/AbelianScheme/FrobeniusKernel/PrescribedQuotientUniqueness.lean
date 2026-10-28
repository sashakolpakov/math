import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessUniqueness

/-! # Prescribed Quotient Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotients of the same independently prescribed kernel classify
the same ordinary point, even when their subgroup representatives differ. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable {D : Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {x y z : D.OrdinaryPoint} {m : ℕ}
variable {kernel : ∀ (T : Over D.integralGeometricBase.left),
  (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop}
variable (Q : D.PrescribedOrdinaryQuotient x m kernel y)
variable (Q' : D.PrescribedOrdinaryQuotient x m kernel z)

theorem Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.representativeKernel :
    Prescribed.Construction.PrescribedKernel Q'.quotient.isogeny.hom Q.inclusion := by
  have : IsClosedImmersion Q.inclusion.left := Q.closed
  have : Mono Q.inclusion := Over.mono_of_mono_left _
  intro T a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := (Q.realizes T a).mpr
      ((Q'.realizes T a).mp ((Q'.quotient.kernel T a).mp ha).exists)
    exact ⟨b, hb, fun b' hb' => (cancel_mono Q.inclusion).mp (hb'.trans hb.symm)⟩
  · intro ha
    have : IsClosedImmersion Q'.inclusion.left := Q'.closed
    have : Mono Q'.inclusion := Over.mono_of_mono_left _
    obtain ⟨b, hb⟩ := (Q'.realizes T a).mpr ((Q.realizes T a).mp ha.exists)
    exact (Q'.quotient.kernel T a).mpr
      ⟨b, hb, fun b' hb' => (cancel_mono Q'.inclusion).mp (hb'.trans hb.symm)⟩

def Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.changeKernelRepresentative :
    D.QuotientWitness (D.pointDatum x.val) m Q.group Q.inclusion where
  target := Q'.quotient.target
  isogeny := Q'.quotient.isogeny
  kernel := Q.representativeKernel Q'
  polarization := Q'.quotient.polarization
  action := Q'.quotient.action
  marking := Q'.quotient.marking

include Q Q' in
theorem Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient.point_eq (hgood : D.IsGoodCompletelySplitReduction) : y = z := by
  apply Subtype.ext
  exact (D.pointOfPEL_eq_of_classifies hgood Q.quotient.target y.val Q.classifies).symm.trans
    ((Q.quotient.point_eq (Q.changeKernelRepresentative Q') hgood).trans
      (D.pointOfPEL_eq_of_classifies hgood Q'.quotient.target z.val Q'.classifies))

include Q in
theorem Integral.Construction.SplitPELReduction.canonicalOrdinaryQuotient_of_witness (hgood : D.IsGoodCompletelySplitReduction) :
    D.CanonicalOrdinaryQuotient x m kernel y :=
  ⟨⟨Q⟩, fun _ h => h.elim (fun Q' => (Q.point_eq Q' hgood).symm)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
