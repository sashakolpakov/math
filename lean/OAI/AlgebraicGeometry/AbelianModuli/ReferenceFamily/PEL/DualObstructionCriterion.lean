import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.PELProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualObstructionCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # Dual Obstruction Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.DualObstructionCriterion

noncomputable section

/-! Zero native deformation obstruction is equivalent to an actual
PEL product, and hence to equality with its constant special-fiber class
in the prescribed-level moduli functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (κ : K →+* ℂ) (A : Objects.PELObject P iota N (ComplexDualTests.pelComplexDualTest κ))

attribute [local instance] Abelian.DualObstructionCriterion.abelianDualFiber_smooth Abelian.DualObstructionCriterion.abelianDualFiber_proper
  Abelian.DualObstructionCriterion.abelianDualFiber_connected Abelian.DualObstructionCriterion.abelianDualFiber_integral Abelian.DualObstructionCriterion.abelianDualH1_complexModule

variable (U : A.polarized.abelian.scheme.left.AffineOpenCover)

theorem pelDualObstruction_zero_normalizedProduct
    (h : Dual.ConormalObstructionLinear.dualConormalObstructionLinear A.polarized.abelian.scheme U = 0) :
    ∃ e : Objects.PELIso A ((A.pullback (ComplexDualTests.pelComplexDualReduction κ)).pullback (ComplexDualTests.pelComplexDualProjection κ)),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e.polarized.abelian := by
  obtain ⟨e, he⟩ := Polarized.DualObstructionCriterion.polarizedDualObstruction_zero_normalizedProduct A.polarized U h
  exact ⟨Normalized.PELProduct.normalizedPELProduct (heGroup := e.abelianGroup) κ A e.abelian he, he⟩

theorem pelDualObstruction_zero_iff_product :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear A.polarized.abelian.scheme U = 0 ↔
      Nonempty (Objects.PELIso A ((A.pullback (ComplexDualTests.pelComplexDualReduction κ)).pullback (ComplexDualTests.pelComplexDualProjection κ))) := by
  constructor
  · intro h
    obtain ⟨e, _⟩ := pelDualObstruction_zero_normalizedProduct κ A U h
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact (Polarized.DualObstructionCriterion.polarizedDualObstruction_zero_iff_product A.polarized U).mpr ⟨e.polarized⟩

theorem pelDualObstruction_zero_iff_class :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear A.polarized.abelian.scheme U = 0 ↔
      (⟦A⟧ : Objects.PELClasses P iota N (ComplexDualTests.pelComplexDualTest κ)) =
        ⟦(A.pullback (ComplexDualTests.pelComplexDualReduction κ)).pullback (ComplexDualTests.pelComplexDualProjection κ)⟧ :=
  (pelDualObstruction_zero_iff_product κ A U).trans
    (Objects.PELObject.classOf_eq_iff A
      ((A.pullback (ComplexDualTests.pelComplexDualReduction κ)).pullback (ComplexDualTests.pelComplexDualProjection κ))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.DualObstructionCriterion
