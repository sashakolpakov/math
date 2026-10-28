import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-! # Total Diagonal -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal

/-! Every diagonal of a first-quadrant bicomplex has finitely many indices. -/

theorem finiteTotalDiagonal (n : ℕ) : Finite {p : ℕ × ℕ // p.1 + p.2 = n} :=
  Finite.of_injective
    (fun p => (⟨p.val.1, by omega⟩ : Fin (n + 1))) (by
      intro a b h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Fin.val h
      · have hf : a.val.1 = b.val.1 := congrArg Fin.val h
        have := a.property
        have := b.property
        omega)

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal
