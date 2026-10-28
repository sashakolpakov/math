import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Etale
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Field Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full-level multiplication is surjective on abelian schemes over fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_surjective_overField (level : A.FullLevel n) :
    Surjective (A.multiplication n).left := by
  have := A.connected_overField
  have := A.fullLevel_multiplication_etale level
  have hcl : IsClopen (Set.range (A.multiplication n).left) :=
    ⟨(A.multiplication n).left.isClosedMap.isClosed_range,
      (A.multiplication n).left.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hcl.eq_univ (Set.range_nonempty _))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
