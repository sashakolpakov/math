import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Frame Free Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFreeModule

noncomputable section

/-!
# IntegralComparison: coefficient vectors for the original finite-frame forms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf.Index σ

local instance frameAlgebra : Algebra W (F).obj.ring := (F).obj.base.toAlgebra

def basis (m : ℕ) : Module.Basis (Index m) (F).obj.ring
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (F).obj.ring (F).obj.ideal (F).obj.dividedPowers m) :=
  (FrameFormBasis.frameBasis p k C σ m).reindex (Fintype.equivFin (Set.powersetCard σ m))

omit [Fintype k] in
theorem basis_apply (m : ℕ) (i : Index m) : basis p k C σ m i =
    FrameFormBasis.frameBasis p k C σ m
      ((Fintype.equivFin (Set.powersetCard σ m)).symm i) :=
  Module.Basis.reindex_apply (FrameFormBasis.frameBasis p k C σ m)
    (Fintype.equivFin (Set.powersetCard σ m)) i

def linearEquiv (m : ℕ) : RelativeCrystalline.FreeModule.freeModule Q (Index m) F ≃ₗ[W]
    RelativeFrame.FormMap.frameModule (F).obj m :=
  (basis p k C σ m).equivFun.symm.restrictScalars W

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFreeModule
