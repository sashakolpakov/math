import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.DegreeBound
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.RationalComparison

/-! # Affine Bound -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineBound.FiniteAffineCohomologyBound

noncomputable section

/-!
# Unconditional cohomological boundedness of finite-type affine crystalline sites

The original integral and rational crystalline cohomology vanish above
the finite number of coordinates in the constructed Witt presentation.
This follows from the proved completed-complex computation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k

def bound : ℕ := Fintype.card (WittFrames.FiniteWittFrames.Variables k B)

theorem integral_isZero (n : ℕ) (hn : bound k B < n) :
    IsZero (ModuleCat.of R (Site.integralCohomology p k X n)) :=
  (Affine.DegreeBound.AffineDegreeBound.homology_isZero p k B (WittFrames.FiniteWittFrames.Variables k B)
    (WittFrames.FiniteWittFrames.reduction k B p) (WittFrames.FiniteWittFrames.reduction_surjective k B p)
    (WittFrames.FiniteWittFrames.reduction_base k B p) n hn).of_iso
      (Affine.FiniteAffineCrystalline.homologyIso p k B n).symm

theorem rational_isZero (n : ℕ) (hn : bound k B < n) :
    IsZero (Site.rationalCohomology p k X n) :=
  ((Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k).map_isZero
    (integral_isZero p k B n hn)).of_iso
      (Affine.RationalComparison.AffineRationalCrystallineComparison.cohomologyModuleIso p k B n).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineBound.FiniteAffineCohomologyBound
