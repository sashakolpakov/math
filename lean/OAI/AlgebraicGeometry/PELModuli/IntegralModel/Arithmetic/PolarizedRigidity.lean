import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ArithmeticCoefficientLocalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalReducedPolarizedRigidity

/-! # Polarized Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PolarizedRigidity

noncomputable section

/-! Realize full-level rigidity over the arithmetic bases of the polarized
moduli problem. The natural denominator and the compatible map of arithmetic
bases are constructed, and the result covers all reduced tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem arithmetic_polarized_reduced_rigidity
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) {S : Scheme.{0}} [IsNoetherian S]
    (p : S ⟶ B.base) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hN : 3 ≤ N) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ (D : ℕ) (hD : D ≠ 0), N ∣ D ∧ B.denominator ∣ D ∧
      let B' := B.withDenominator D hD
      ∃ b : B'.base ⟶ B.base, B'.generic ≫ b = B.generic ∧
        ∀ {T : Scheme.{0}} [IsReduced T] (t : T ⟶ S) (q : T ⟶ B'.base),
          t ≫ p = q ≫ b →
          ∀ e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (A.pullback t),
            e.abelian.hom = 𝟙 (A.abelian.pullback t).scheme := by
  have : IsDomain B.R := Function.Injective.isDomain B.toField B.toField_injective
  have : Countable B.extension.carrier := AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ B.extension.carrier
  obtain ⟨r, hr, hrigid⟩ := GlobalReducedPolarizedRigidity.polarized_reduced_rigidity_away B.toField B.toField_injective p A hN hPresentations
  obtain ⟨D, hD, hND, hBD, φ, hφ, hunit⟩ :=
    B.coefficient_isUnit_after_localization r hr N (by omega)
  let B' := B.withDenominator D hD
  let b : B'.base ⟶ B.base := Spec.map (CommRingCat.ofHom φ)
  have hb : B'.generic ≫ b = B.generic := by
    change Spec.map (CommRingCat.ofHom B'.toField) ≫ Spec.map (CommRingCat.ofHom φ) = _
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hφ
  refine ⟨D, hD, hND, hBD, b, hb, ?_⟩
  intro T _ t q hbase e
  have : IsReduced (Over.mk t).left := inferInstanceAs (IsReduced T)
  apply hrigid (Over.mk t) e
  intro x hbad
  have hx : p (t x) = b (q x) := congrArg (fun f : T ⟶ B.base => f x) hbase
  have hmem : φ r ∈ (q x).asIdeal :=
    (congrArg (fun z : B.base => r ∈ z.asIdeal) hx).mp hbad
  exact (q x).isPrime.ne_top ((q x).asIdeal.eq_top_of_isUnit_mem hmem hunit)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PolarizedRigidity
