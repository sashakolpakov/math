import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Containment Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentBaseChange

/-! Containment of the full isogeny kernel in integer torsion persists under arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S T : Scheme.{u}} {a b : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ)
  (hf : ∀ (U : Over S) (x : U ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)

include hf

/-- All points over the new base are points over the original base through the base-change adjunction. -/
theorem contained (s : T ⟶ S) (U : Over T) (x : U ⟶ (A.pullback s).scheme)
    (hx : x ≫ (f.pullback s).hom = 1) : x ^ n = 1 := by
  have h : A.baseChangePointsEquiv s U x ≫ f.hom = 1 :=
    (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f.hom s U x).symm.trans
      ((congrArg (B.baseChangePointsEquiv s U) hx).trans (B.baseChangePointsMulEquiv s U).map_one)
  apply (A.baseChangePointsMulEquiv s U).injective
  rw [map_pow, map_one]
  exact hf ((Over.map s).obj U) (A.baseChangePointsEquiv s U x) h

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentBaseChange
