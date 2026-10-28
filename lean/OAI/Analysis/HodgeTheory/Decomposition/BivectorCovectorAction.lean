import OAI.Analysis.HodgeTheory.Decomposition.CovariantInsertion
import OAI.Analysis.HodgeTheory.Decomposition.BivectorContraction

/-! # Bivector Covector Action -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BivectorCovectorAction.Constructions

noncomputable section

/-! The infinitesimal covector action on a finite bivector contraction. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem bivectorContraction_covectorAction (n : ℕ) (A : E →L[ℝ] E)
    (u v : ι → E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    BivectorContraction.Constructions.bivectorContraction n u v (CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1 + 1) A a) =
      CovectorConnection.Constructions.covectorInfinitesimalAction n A (BivectorContraction.Constructions.bivectorContraction n u v a) +
        BivectorContraction.Constructions.bivectorContraction n (fun i => A (u i)) v a +
        BivectorContraction.Constructions.bivectorContraction n u (fun i => A (v i)) a := by
  simp only [BivectorContraction.Constructions.bivectorContraction_apply, map_sum]
  simp_rw [CovariantInsertion.Constructions.covectorInfinitesimalAction_contraction (n + 1) A, map_add,
    CovariantInsertion.Constructions.covectorInfinitesimalAction_contraction n A]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  abel

end

end OAI.Analysis.HodgeTheory.Decomposition.BivectorCovectorAction.Constructions
