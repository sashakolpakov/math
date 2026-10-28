import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContraction
import OAI.Analysis.DifferentialForms.Manifold.Bidegree

/-! # Antiholomorphic Contraction Purity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionPurity.Dolbeault

noncomputable section

/-! Antiholomorphic contraction lowers exactly the antiholomorphic degree
of the original pure alternating covectors. -/

open _root_.ContinuousAlternatingMap

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem antiContraction_pullback (n : ℕ) (v : E) (L : E →L[ℂ] F)
    (a : F [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (a.compContinuousLinearMap (L.restrictScalars ℝ)) =
      (AntiholomorphicContraction.Dolbeault.antiContraction n (L v) a).compContinuousLinearMap (L.restrictScalars ℝ) := by
  ext w
  rw [AntiholomorphicContraction.Dolbeault.antiContraction_apply]
  change (1 / 2 : ℂ) *
      (a (fun j : Fin (n + 1) => L ((Fin.cons v w : Fin (n + 1) → E) j)) +
        Complex.I * a (fun j : Fin (n + 1) =>
          L ((Fin.cons (Complex.I • v) w : Fin (n + 1) → E) j))) =
    AntiholomorphicContraction.Dolbeault.antiContraction n (L v) a (fun j : Fin n => L (w j))
  have hcons (u : E) :
      (fun j : Fin (n + 1) => L ((Fin.cons u w : Fin (n + 1) → E) j)) =
        (Fin.cons (L u) (fun j : Fin n => L (w j)) : Fin (n + 1) → F) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  rw [hcons, hcons, L.map_smul, AntiholomorphicContraction.Dolbeault.antiContraction_apply]

theorem antiContraction_scalarPullback (n : ℕ) (v : E) (z : ℂ)
    (a : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E (n + 1) z a) =
      (star z) • Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z (AntiholomorphicContraction.Dolbeault.antiContraction n v a) := by
  have h := antiContraction_pullback n v (ContinuousLinearMap.lsmul ℂ ℂ z) a
  change AntiholomorphicContraction.Dolbeault.antiContraction n v (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E (n + 1) z a) =
    Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z (AntiholomorphicContraction.Dolbeault.antiContraction n (z • v) a) at h
  rw [AntiholomorphicContraction.Dolbeault.antiContraction_smul_direction, map_smul] at h
  exact h

theorem antiContraction_pure (p q : ℕ) (v : E)
    (a : E [⋀^Fin (p + q + 1)]→L[ℝ] ℂ) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p (q + 1) a) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (AntiholomorphicContraction.Dolbeault.antiContraction (p + q) v a) := by
  intro z w
  have hp : Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E (p + q + 1) (z : ℂ) a = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z • a := by
    ext u
    exact ha z u
  have h := antiContraction_scalarPullback (p + q) v (z : ℂ) a
  rw [hp, map_smul] at h
  have hv := congrArg (fun b : E [⋀^Fin (p + q)]→L[ℝ] ℂ => b w) h
  change Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) z * AntiholomorphicContraction.Dolbeault.antiContraction (p + q) v a w =
    star (z : ℂ) * AntiholomorphicContraction.Dolbeault.antiContraction (p + q) v a (fun i => (z : ℂ) • w i) at hv
  apply mul_left_cancel₀ (star_ne_zero.mpr z.ne_zero)
  rw [← hv]
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_succ]
  ring

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionPurity.Dolbeault
