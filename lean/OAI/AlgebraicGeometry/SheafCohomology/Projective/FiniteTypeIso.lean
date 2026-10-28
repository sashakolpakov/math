import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Finite Type Iso -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTypeIso

noncomputable section

/-! Finite local generators transport through an actual module isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem finiteType_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let p : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i =>
        (SheafOfModules.GeneratingSections.equivOfIso
          ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e))
          (q.generators i) }
  have hp : p.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite (q.generators i).I
    exact (hq.isFiniteType i).finite
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨p, hp⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTypeIso
