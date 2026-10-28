import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Frame Free Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFreeModule

noncomputable section

/-!
# IntegralComparison: coefficient vectors for the original finite-frame forms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  BoundedSmooth.WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf.Index σ

local instance frameAlgebra : Algebra W (F).obj.ring := (F).obj.base.toAlgebra

def basis (m : ℕ) : Module.Basis (Index m) (F).obj.ring
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (F).obj.ring (F).obj.ideal (F).obj.dividedPowers m) :=
  (FrameFormBasis.frameBasis p k A σ n C ρ hρ hker hbase m).reindex (Fintype.equivFin (Set.powersetCard σ m))

theorem basis_apply (m : ℕ) (i : Index m) : basis p k A C σ ρ hρ hker hbase n m i =
    FrameFormBasis.frameBasis p k A σ n C ρ hρ hker hbase m
      ((Fintype.equivFin (Set.powersetCard σ m)).symm i) :=
  Module.Basis.reindex_apply (FrameFormBasis.frameBasis p k A σ n C ρ hρ hker hbase m)
    (Fintype.equivFin (Set.powersetCard σ m)) i

def linearEquiv (m : ℕ) : RelativeCrystalline.FreeModule.freeModule Q (Index m) F ≃ₗ[W]
    RelativeFrame.FormMap.frameModule (F).obj m :=
  (basis p k A C σ ρ hρ hker hbase n m).equivFun.symm.restrictScalars W

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFreeModule
