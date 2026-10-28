import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking

/-! # Period Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking

noncomputable section

/-! An E-linear change between the constructed rank-three markings
induces the actual rational period isomorphism. Its integral condition
is exactly preservation of the constructed marked lattices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def markedPeriodTransport (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B PB σ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B PB σ
  exact ((Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A PA ρ s hs hg hdegree).trans
    (u.trans (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree).symm)).restrictScalars ℚ

theorem markedPeriodTransport_coordinates (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree (markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u v) =
      u (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A PA ρ s hs hg hdegree v) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B PB σ
  exact (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree).apply_symm_apply _

theorem coordinates_mem_markedLattice (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A PA ρ s hs hg hdegree v ∈ Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A PA ρ s hs hg hdegree ↔
      v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A PA ρ
  let c := Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A PA ρ s hs hg hdegree
  change c v ∈ (Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)).map (c.restrictScalars ℤ).toLinearMap ↔ _
  rw [Submodule.mem_map_equiv]
  exact (congrArg (fun w => w ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) (c.symm_apply_apply v)).to_iff

theorem markedPeriodTransport_integral (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x, x ∈ Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A PA ρ s hs hg hdegree ↔
      u x ∈ Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B PB σ s hs hg hdegree)
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ↔
      markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) := by
  have ha := coordinates_mem_markedLattice A PA ρ s hs hg hdegree v
  have hb := coordinates_mem_markedLattice B PB σ s hs hg hdegree
    (markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u v)
  rw [markedPeriodTransport_coordinates] at hb
  exact ha.symm.trans ((hu _).trans hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking
