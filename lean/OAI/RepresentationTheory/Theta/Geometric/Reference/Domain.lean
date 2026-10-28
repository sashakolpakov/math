import OAI.RepresentationTheory.Theta.Geometric.Data
import OAI.NumberTheory.ArithmeticGroups.Diagonal
import OAI.RepresentationTheory.Theta.Geometric.CompactLattice

/-! # Domain -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The native matrix ball is exactly the negative-line domain of the
supplied PEL reference lattice. Its period fibers retain that same lattice,
polarization, and integral CM action. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.reference_domain_eq : D.pel.reference.domain = (D.domain : Set LinearTheta.BallCoordinates) := by
  ext x
  change (Geometry.ComplexBall.PrescribedSignsB.localB D.pel.reference.embeddings (Matrix.diagonal ![1, 1, D.pel.reference.b])
    D.pel.reference.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector x) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector x))).re < 0 ↔
      Complex.normSq (x 0) + Complex.normSq (x 1) < -(D.pel.reference.μ D.pel.reference.b).re
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real]
  simp only [Geometry.ComplexBall.PrescribedSignsB.lineVector, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  change Complex.normSq (x 0) + Complex.normSq (x 1) +
      (D.pel.reference.μ D.pel.reference.b).re * Complex.normSq 1 < 0 ↔ _
  rw [Complex.normSq_one, mul_one]
  constructor <;> intro h <;> linarith

theorem Data.ActiveHeckeThetaData.reference_analytic_fiber (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.AnalyticPolarizedFiber D.pel.reference.embeddings D.pel.reference.lattice
      D.pel.reference.traceForm (D.pel.reference.periodFamily x.val) := by
  rcases hg.reference_admissible with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hperiod⟩
  exact (hperiod x.val (by rw [D.reference_domain_eq]; exact x.property)).2

end

end OAI.RepresentationTheory.Theta.Geometric
