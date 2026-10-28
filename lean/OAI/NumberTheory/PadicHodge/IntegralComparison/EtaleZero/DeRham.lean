import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameDeRhamIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamComplex

/-! # De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.DeRham.Comparison

noncomputable section

/-!
# IntegralComparison: original zeroth-level crystalline cohomology is ordinary étale-chart de Rham cohomology

The comparison retains the canonical frame section map and both original
coefficient lifts. The source is the ordinary residue-field de Rham
complex with scalars restricted along the actual Witt residue map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C]

local notation "W" => WittVector p k
local notation "CoeffW" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

def coefficientFunctor : ModuleCat.{u} W ⥤ ModuleCat.{u + 2} CoeffW :=
  Crystalline.RelativeResolution.coefficientFunctor (B := W) ⋙ ModuleCat.uliftFunctor.{u + 2, u + 1} CoeffW

instance coefficientFunctor_additive : (coefficientFunctor p k).Additive := by
  dsimp [coefficientFunctor]
  infer_instance

def deRhamComplex : CochainComplex (ModuleCat.{u + 2} CoeffW) ℕ :=
  ((coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (ZeroLevel.DeRhamComplex.residueComplex p k C)

def frameIso : BoundedEtale.ZeroFrameDeRhamIso.frameComplex p k C ≅ deRhamComplex p k C :=
  ((coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (ZeroLevel.DeRhamComplex.frameComplexIso p k C)

variable (σ : Type u) [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]

def homologyIso (i : ℕ) : (deRhamComplex p k C).homology i ≅
    ModuleCat.of CoeffW (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0 i) :=
  ((HomologicalComplex.homologyFunctor _ _ i).mapIso (frameIso p k C)).symm ≪≫
    BoundedEtale.ZeroFrameDeRhamIso.homologyIso p k C σ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.DeRham.Comparison
