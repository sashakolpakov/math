import Mathlib

/-! # Finite Type Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeQuotient

noncomputable section

/-! Finite type passes to the actual quotient using the images of finite local generators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

theorem of_epi [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent]
    (f : M ⟶ N) [hf : Epi f] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let p : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i => by
        let : Epi (f.over (q.X i)) := by
          change Epi ((SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over (q.X i)))).map f)
          exact @Functor.PreservesEpimorphisms.preserves _ _ _ _ _
            (Functor.preservesEpimorphisms_of_adjunction
              (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) (q.X i))) M N f hf
        exact (q.generators i).ofEpi (f.over (q.X i)) }
  have hp : p.IsFiniteType := by
    constructor
    intro i
    exact ⟨(hq.isFiniteType i).finite⟩
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨p, hp⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeQuotient
