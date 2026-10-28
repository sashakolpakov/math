import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames

/-! # Big Affine -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.BigAffine.FiniteBigAffineCrystalline

noncomputable section

/-! # Unconditional completed-frame computation of original big affine crystalline Ext -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

local notation "σ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.Variables k B
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.reduction k B p
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.reduction_surjective k B p
local notation "hbase" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames.FiniteWittFrames.reduction_base k B p
local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hbase

def homologyIso (n : ℕ) : (complex p k B).homology n ≅
    ModuleCat.of R (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := I) (δ := γ) bX n) := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact Big.AffineComparison.BigAffineCrystallineComparison.homologyIso p k B σ r hr hbase n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.BigAffine.FiniteBigAffineCrystalline
