import OAI.AlgebraicGeometry.Comparison.Betti.Closed.FormAntiholomorphicDirections
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultSquared

/-! # Dolbeault Correction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.DolbeaultCorrection

noncomputable section

/-! Subtracting the genuine Dolbeault derivative of a primitive preserves
closedness and pure type, and cancels a prescribed contraction. -/

open _root_.TopologicalSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {U : Opens E}

def correctOpenDolbeaultForm (n : ℕ) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1) :=
  a - DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u

theorem correctOpenDolbeaultForm_closed (n p q : ℕ) (hn : n = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0)
    (u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) (hu : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q u) :
    DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) (correctOpenDolbeaultForm n a u) = 0 := by
  have hs : correctOpenDolbeaultForm n a u = a + (-1 : ℂ) • DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u := by
    ext x v
    change a x v - DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u x v =
      a x v + (-1 : ℂ) * DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u x v
    ring
  rw [hs, map_add, map_smul, ha,
    DivisorClass.Chern.Open.DolbeaultSquared.openDolbeaultD_squared_of_bidegree u hn hu, smul_zero, add_zero]

theorem correctOpenDolbeaultForm_pure (n p q : ℕ) (hn : n = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (ha : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a)
    (u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) (hu : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q u) :
    DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) (correctOpenDolbeaultForm n a u) := by
  have hd := DivisorClass.Chern.Open.DolbeaultPrime.openDolbeaultD_hasBidegree hn hu
  intro x z v
  change a x (fun i => (z : ℂ) • v i) - DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u x (fun i => (z : ℂ) • v i) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z * (a x v - DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u x v)
  rw [ha x z v, hd x z v, mul_sub]

theorem correctOpenDolbeaultForm_contraction (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 2)) (u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (hu : AntiholomorphicContraction.Dolbeault.openAntiContraction U n v u = 0) (x : U) :
    AntiholomorphicContraction.Dolbeault.openAntiContraction U (n + 1) v (correctOpenDolbeaultForm (n + 1) a u) x =
      AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v (a x) - VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative u.extension x v := by
  have hc := AntiholomorphicContraction.Dolbeault.openDolbeaultD_antiContraction n v u x
  rw [hu, map_zero, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply, zero_add] at hc
  rw [AntiholomorphicContraction.Dolbeault.openAntiContraction_apply]
  change AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v (a x - DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) u x) = _
  rw [map_sub]
  rw [AntiholomorphicContraction.Dolbeault.openAntiContraction_apply] at hc
  rw [hc]
  rfl

theorem correctOpenDolbeaultForm_contraction_zero (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 2)) (u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (hu : AntiholomorphicContraction.Dolbeault.openAntiContraction U n v u = 0)
    (hprim : ∀ x : U, VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative u.extension x v = AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v (a x)) :
    AntiholomorphicContraction.Dolbeault.openAntiContraction U (n + 1) v (correctOpenDolbeaultForm (n + 1) a u) = 0 := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [correctOpenDolbeaultForm_contraction n v a u hu x, hprim x, sub_self]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.DolbeaultCorrection
