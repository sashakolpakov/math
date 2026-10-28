import OAI.Analysis.PDE.Energy.Rank.Energy.PeriodicSign
import OAI.LinearAlgebra.Moore.MooreRankDeterminant

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem correction_nonpos_of_background_rank {n s r : ℕ} (hr : r < n)
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosDef)
    (hback : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hrank : ∀ x ∈ S, OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) :
    ∀ x ∈ closure S, u x ≤ 0 :=
  correction_nonpos_of_singular_background e hS hb hB hu hz hpos
    (fun x hx => OAI.LinearAlgebra.Moore.mooreDet_eq_zero_of_rank_lt _ (hback x hx) (hrank x hx) hr)

theorem correction_nonpos_rank_representatives {n s r : ℕ} (hrankdim : r < n)
    (e : Fin s → Quaternion ℝ) {B u ρ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    {K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hK : IsCompact K) (hKD : K ⊆ {x | ρ x ≤ 0}) (hρ : Continuous ρ)
    (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (hrep : ∀ x, ρ x ≤ 0 → p x ∈ K)
    (hup : ∀ x, ρ x ≤ 0 → u (p x) = u x)
    (hpos : ∀ x, ρ x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosDef)
    (hback : ∀ x, ρ x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hrank : ∀ x, ρ x < 0 → OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x))
    (hbd : ∀ x, ρ x = 0 → u x = 0) : ∀ x, ρ x ≤ 0 → u x ≤ 0 :=
  correction_nonpos_singular_representatives e p hK hKD hρ hB hu hrep hup hpos
    (fun x hx => OAI.LinearAlgebra.Moore.mooreDet_eq_zero_of_rank_lt _ (hback x hx) (hrank x hx) hrankdim) hbd

/-- Source upper estimate, including the derivation of the sign from rank. -/
theorem rank_energy_sharp_upper {n s r : ℕ} (hr : r < n)
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosDef)
    (hback : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hrank : ∀ x ∈ S, OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x))
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (determinantMass e S (fun y => B y + u y) u + determinantSegmentEnergy e S B u) / Λ ≤
      (n : ℝ)/((n : ℝ)+1) * (determinantMass e S (fun y => B y + u y) u / Λ) := by
  have hn := correction_nonpos_of_background_rank hr e hS hb
    (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) hz hpos hback hrank
  exact normalized_determinant_energy_sharp_upper e hS.measurableSet hb hB hu
    (fun x hx => hn x (subset_closure hx)) (fun x hx => (hpos x hx).posSemidef) hback hΛ

end OAI.Analysis.PDE.Energy
