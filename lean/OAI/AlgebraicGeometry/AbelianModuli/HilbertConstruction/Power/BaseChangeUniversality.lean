import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Base Change Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Arbitrary pullback preserves the universal tensor-power property of line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L : Line.Bundles.LineBundle Y} {P : Y.Modules} {n : ℕ}

theorem Tensor.Powers.IsTensorPower.pullback_lineBundle (hP : Tensor.Powers.IsTensorPower L.sheaf n P) (f : X ⟶ Y) :
    Tensor.Powers.IsTensorPower (L.pullback f).sheaf n ((Scheme.Modules.pullback f).obj P) := by
  obtain ⟨e⟩ := hP.unique (L.tensorPower_isTensorPower n)
  exact ((L.pullback f).tensorPower_isTensorPower n).of_targetIso
    ((Line.Bundles.LineBundle.powerBaseChangeIso f L n).symm ≪≫ (Scheme.Modules.pullback f).mapIso e.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
