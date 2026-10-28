import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableGroupFibers
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedIntrinsicPresentation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedLevel

/-! # Period Fiber Countability -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodFiberCountability

noncomputable section

/-! Equal fixed coefficient periods identify the actual native
marked kernels. Native algebraization and faithful fine PEL counting
therefore prove countability of every coefficient-period fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

theorem PEL_period_fibers_countable
    {E K Q : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N r n : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (basis : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (p : Q → (Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ M.space))
    (hp : Function.Injective p)
    (b : ∀ q, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n)
      (PolarizedIntrinsicPresentation.polarizedNativePresentation (M.universal.pullback (p q)).polarized).variety)
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (C : (Fin n → ℂ) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (period : Q → Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hperiod : ∀ q v, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b q) v = 0 ↔
      ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector (period q))) (C v)) :
    ∀ z : Geometry.ComplexBall.PrescribedSignsB.BallChart, {q : Q | period q = z}.Countable := by
  intro z
  let J := {q : Q // period q = z}
  by_cases hn : Nonempty J
  · let q₀ : J := Classical.choice hn
    have hker (q : J) : (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b q₀)).ker = (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b q)).ker := by
      ext v
      change ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b q₀) v = 0 ↔ ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b q) v = 0
      rw [hperiod, hperiod, q₀.property, q.property]
    choose f hf hmark using (fun q : J => ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.algebraic_iso_of_marked_period_eq
      _ _ (b q₀) (b q) (hker q))
    let (q : J) : IsMonHom (f q).hom := hf q
    let B := fun q : Q => (M.universal.pullback (p q)).polarized
    let present := fun q => PolarizedIntrinsicPresentation.polarizedNativePresentation (B q)
    let iso := fun q : J => ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso (present q₀) (present q) (f q)
    have hiso (q : J) : IsMonHom (iso q).hom :=
      ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso_group (present q₀) (present q) (f q)
    have hcount := CountableGroupFibers.countable_PEL_classifying_maps_of_group_isos M hM κ basis
      (fun q : J => p q) (B q₀) (present q₀) (fun q : J => present q) iso hiso
    apply (hcount.preimage hp).mono
    intro q hq
    exact ⟨⟨q, hq⟩, rfl⟩
  · let : IsEmpty J := not_nonempty_iff.mp hn
    exact Set.countable_coe_iff.mp (inferInstanceAs (Countable J))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodFiberCountability
