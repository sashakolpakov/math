import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Projectives
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Flat

/-! # Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Tor

noncomputable section

/-! The categorical Tor modules of two finitely generated modules over a
Noetherian ring are finitely generated. Compute in the abelian category of
finite modules and compare its projective resolutions with all modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Projectives

def inclusionTensorIso (M : FGModuleCat.{u} R) :
    Projectives.inclusion R ⋙ tensorLeft M.obj ≅ tensorLeft M ⋙ Projectives.inclusion R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def finiteTorIso (M N : FGModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M.obj).obj N.obj ≅
      (((Tor (FGModuleCat R) n).obj M).obj N).obj :=
  DerivedBaseChange.leftDerivedIso (tensorLeft M) (tensorLeft M.obj)
    (Projectives.inclusion R) (Projectives.inclusion R) (inclusionTensorIso R M) N n

theorem finite (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (n : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) n).obj M).obj N) := by
  let e := finiteTorIso R (FGModuleCat.of R M) (FGModuleCat.of R N) n
  exact Module.Finite.equiv e.toLinearEquiv.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Tor
