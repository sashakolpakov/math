import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProgramCorrectness

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpProgramCorrectness

noncomputable section

section BooleanTables

variable {V E I R : Type*} [DecidableEq V] [Fintype I]
  [CommRing R] {p m : ℕ}

/-- Enumerating every finite label row of the input Boolean table supplies
the local table identity used by the program-correctness theorem. -/
theorem fullRows_eq_interpolatedTable
    (S : Factor.System V E I) (e : E)
    (scope : Fin m ≃ {v // v ∈ S.scope e}) (labels : Fin p ≃ I)
    (lift : I → R) (hu : TableInterpolation.UnitDifferences lift) :
    SubexpTableInterpolation.tablePolynomial (fun i => lift (labels i))
      (SubexpTableInterpolation.reindexedUnits labels lift hu)
      (SubexpTableInterpolation.fullRows (fun a =>
        if S.table e (fun v => labels (a.get (scope.symm v))) = true then 1 else 0)) =
      MvPolynomial.rename scope.symm (GlobalPolynomial.interpolatedTable S lift hu e) := by
  classical
  unfold GlobalPolynomial.interpolatedTable
  exact SubexpTableInterpolation.fullRows_reindexed scope labels lift hu
    (fun a => if S.table e a = true then (1 : R) else 0)

end BooleanTables

end

end SubexponentialSAT.SubexpProgramCorrectness

end OAI.Algorithms
