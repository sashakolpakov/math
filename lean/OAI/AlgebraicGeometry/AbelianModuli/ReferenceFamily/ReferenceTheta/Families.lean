import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationFactor
import OAI.RepresentationTheory.Theta.Geometric.ConsecutiveEmbeddings

/-! # Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Construct consecutive embedding families for the exact reference
polarization before applying the algebraic model comparison. -/

open OAI.RepresentationTheory.Theta.Geometric.ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

theorem Reference.Fiber.ReferenceAnalyticFiber.exists_consecutive_theta_families : ∃ U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP),
    0 < U.degree ∧ V.degree = U.degree + 1 ∧
    Function.Injective U.projectiveMap ∧ Function.Injective V.projectiveMap ∧
    (∀ p v : F.periodData.space, v ≠ 0 → U.Detects p v) ∧
    ∀ p v : F.periodData.space, v ≠ 0 → V.Detects p v := by
  have hint : ∀ u ∈ F.periodData.periodIntegerLattice, ∀ v ∈ F.periodData.periodIntegerLattice,
      ∃ m : ℤ, (F.form u v).im = (m : ℝ) :=
    fun u hu v hv => F.form_integral hP ⟨u, hu⟩ ⟨v, hv⟩
  exact RepresentationTheory.Theta.Geometric.ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta.exists_consecutive_embeddings (Φ := F.periodData) F.form F.hermitian F.positive hint
    (F.polarizationFactor hP) (F.polarizationFactor_contDiff hP)
    (F.polarizationFactor_square hP) (F.polarizationFactor_double_lattice hP)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
