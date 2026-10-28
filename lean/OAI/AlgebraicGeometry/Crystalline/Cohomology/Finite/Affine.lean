import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames

/-! # Affine -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.Affine.FiniteAffineCrystalline

noncomputable section

/-!
# The unconditional finite-type affine crystalline computation

The constructed finite Witt presentation supplies the original p-power
PD envelope tower. Its completed PD de Rham complex computes original
integral crystalline cohomology in every degree, with no additional
presentation, acyclicity, or comparison assumption.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

local notation "σ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.Variables k B
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.reduction k B p
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.reduction_surjective k B p
local notation "hbase" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.reduction_base k B p
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hbase

def homologyIso (n : ℕ) : (complex p k B).homology n ≅
    ModuleCat.of R (Site.integralCohomology p k X n) := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact Affine.Comparison.AffineCrystallineComparison.homologyIso p k B σ r hr hbase n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.Affine.FiniteAffineCrystalline
