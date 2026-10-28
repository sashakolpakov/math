import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames

/-! # Section Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.SectionComparison.FiniteCrystallineSectionComparison

noncomputable section

/-!
# Affine crystalline sections with the constructed finite Witt presentation

Every finite-type residue algebra has the already constructed finite
polynomial Witt presentation. Its actual frame-resolution section
complex computes the original integral crystalline cohomology, without
asking for an additional presentation or acyclicity hypothesis.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison.ordinaryComplex p k B (WittFrames.FiniteWittFrames.Variables k B)
    (WittFrames.FiniteWittFrames.reduction k B p)

def homologyIso (n : ℕ) : (complex p k B).homology n ≅
    ModuleCat.of R (Site.integralCohomology p k X n) :=
  CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison.ordinaryHomologyIso p k B (WittFrames.FiniteWittFrames.Variables k B)
    (WittFrames.FiniteWittFrames.reduction k B p) (WittFrames.FiniteWittFrames.reduction_surjective k B p)
    (WittFrames.FiniteWittFrames.reduction_base k B p) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.SectionComparison.FiniteCrystallineSectionComparison
