import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PolarizedRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

/-! # Iso Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.IsoRigidity

noncomputable section

/-! Full-level rigidity determines the entire polarized isomorphism,
including its dual component. This is the uniqueness needed for descent
of actual universal families and their comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

theorem polarizedIso_eq_of_source_rigidity
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    {A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (hA : ∀ e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A, e.abelian.hom = 𝟙 A.abelian.scheme)
    (a b : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) : a = b := by
  apply AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  have h := hA (a.trans b.symm)
  change a.abelian.hom ≫ b.abelian.inv = 𝟙 A.abelian.scheme at h
  have he := congrArg (· ≫ b.abelian.hom) h
  exact ((Category.assoc _ _ _).trans
    ((congrArg (a.abelian.hom ≫ ·) b.abelian.inv_hom_id).trans
      (Category.comp_id _))).symm.trans (he.trans (Category.id_comp _))

theorem arithmetic_polarized_isomorphism_unique
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
          ∀ C : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T,
            Subsingleton (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) C) := by
  obtain ⟨D, hD, hND, hBD, b, hb, hrigid⟩ := Arithmetic.PolarizedRigidity.arithmetic_polarized_reduced_rigidity B p A hN hPresentations
  refine ⟨D, hD, hND, hBD, b, hb, ?_⟩
  intro T _ t q hbase C
  exact ⟨polarizedIso_eq_of_source_rigidity (hrigid t q hbase)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.IsoRigidity
