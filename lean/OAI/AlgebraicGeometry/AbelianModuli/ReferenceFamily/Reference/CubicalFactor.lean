import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationFactor
import OAI.RepresentationTheory.Theta.Geometric.Cubical.PullbackFactors

/-! # Cubical Factor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The primitive reference polarization factor satisfies the exact
cubical identity, directly from the original alternating integral form. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

theorem Fiber.ReferenceAnalyticFiber.polarizationFactor_isCubical : (F.polarizationFactor hP).IsCubical := by
  intro l m n w v u
  have H := RepresentationTheory.Theta.Geometric.Cubical.Automorphy.polarizationAutomorphy_cube F.form (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding (Fiber.ReferenceAnalyticFiber.referenceForm_isAlt hP) F.hermitian (F.latticeEquiv_polarization hP)
    (F.integralLatticeEquiv.symm l) (F.integralLatticeEquiv.symm m) (F.integralLatticeEquiv.symm n) w v u
  simp only [Fiber.ReferenceAnalyticFiber.polarizationFactor, map_add]
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
