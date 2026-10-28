import OAI.Analysis.PDE.Energy.Rank.Energy.Upper
import OAI.LinearAlgebra.Moore.Form

/-! The sign of the Dirichlet correction follows from the singularity of
the background Hessian, rather than being an additional energy assumption. -/

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology MatrixOrder ComplexOrder

theorem not_localMax_of_singular_background {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hpos : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosDef)
    (hsing : OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0) : ¬ IsLocalMax u x := by
  intro hm
  have hn := OAI.LinearAlgebra.Moore.complexify_hessianMap_posSemidef e
    (OAI.Analysis.PDE.Dirichlet.realHessian_neg_posSemidef_of_localMax hu hm)
  have he : OAI.Analysis.Calculus.Quaternion.hessianMap e (-OAI.Analysis.PDE.Dirichlet.realHessian u x) = -OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x := by
    rw [← neg_one_smul ℝ (OAI.Analysis.PDE.Dirichlet.realHessian u x), OAI.Analysis.Calculus.Quaternion.hessianMap_smul]
    simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, neg_one_smul]
  rw [he] at hn
  have heq : OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun z => B z + u z) x + -OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x := by
    rw [hessian_sum e hB hu]
    abel
  have hp : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosDef := by
    rw [heq, OAI.LinearAlgebra.Moore.complexify_add]
    exact hpos.add_posSemidef hn
  have hd := OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef _ hp
  rw [hsing] at hd
  exact lt_irrefl _ hd

theorem correction_nonpos_of_singular_background {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosDef)
    (hsing : ∀ x ∈ S, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0) :
    ∀ x ∈ closure S, u x ≤ 0 := by
  intro x hx
  have hc : IsCompact (closure S) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn ⟨x, hx⟩ hu.continuous.continuousOn
  by_cases hys : y ∈ S
  · have hm : IsLocalMax u y := hmax.isLocalMax
      (Filter.mem_of_superset (hS.mem_nhds hys) subset_closure)
    exact False.elim (not_localMax_of_singular_background e hB hu (hpos y hys) (hsing y hys) hm)
  · have hyf : y ∈ frontier S := by
      rw [frontier, hS.interior_eq]
      exact ⟨hy, hys⟩
    exact (hmax hx).trans_eq (hz y hyf)

end OAI.Analysis.PDE.Energy
