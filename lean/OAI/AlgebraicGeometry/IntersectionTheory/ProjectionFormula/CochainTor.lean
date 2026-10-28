import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MapExtend
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.TensorSingle

/-! # Cochain Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CochainTor

noncomputable section

/-! The cochain tensor columns compute the same native Tor modules as the
original projective resolutions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R] (M N : ModuleCat.{0} R) (P : ProjectiveResolution N)

def iso (n : ℕ) :
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj
      (ChainToCochain.cochain R P.complex)).homology (-(n : ℤ)) ≅
      ((Tor (ModuleCat.{0} R) n).obj M).obj N :=
  MapExtend.cochainHomologyIso R (tensorLeft M) P.complex n ≪≫
    (P.isoLeftDerivedObj (tensorLeft M) n).symm

def singleIso (d : ℤ) (n : ℕ) :
    ((Tensor.Homotopy.complexFunctor R (ChainToCochain.cochain R P.complex)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).obj M)).homology (d - (n : ℤ)) ≅
      ((Tor (ModuleCat.{0} R) n).obj M).obj N :=
  Tensor.TensorSingle.homologyIso R M (ChainToCochain.cochain R P.complex) d (d - (n : ℤ)) ≪≫
    eqToIso (by congr 1; omega) ≪≫ iso R M N P n

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CochainTor
