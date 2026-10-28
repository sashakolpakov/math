import Mathlib

/-! # Finite Type Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeIso

noncomputable section

/-! Finite local generators transport through the actual isomorphism of scheme modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) [M.IsFiniteType]

include e in
theorem finiteType : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let p : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i => (SheafOfModules.GeneratingSections.equivOfIso
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e)) (q.generators i) }
  have hp : p.IsFiniteType := by
    constructor
    intro i
    exact ⟨(hq.isFiniteType i).finite⟩
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨p, hp⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeIso
