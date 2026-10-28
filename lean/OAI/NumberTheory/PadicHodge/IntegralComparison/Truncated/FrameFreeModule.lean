import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Frame Free Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameFreeModule

noncomputable section

/-!
# IntegralComparison: coefficient vectors for the original finite-frame forms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  BoundedTruncated.FrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormPresheaf.Index σ

local instance frameAlgebra : Algebra W (F).obj.ring := (F).obj.base.toAlgebra

def basis (m : ℕ) : Module.Basis (Index m) (F).obj.ring
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (F).obj.ring (F).obj.ideal (F).obj.dividedPowers m) :=
  (FrameFormBasis.frameBasis p k n A σ C ρ hρ hker hbase m).reindex (Fintype.equivFin (Set.powersetCard σ m))

omit [Fintype k] in
theorem basis_apply (m : ℕ) (i : Index m) : basis p k n A C σ ρ hρ hker hbase m i =
    FrameFormBasis.frameBasis p k n A σ C ρ hρ hker hbase m
      ((Fintype.equivFin (Set.powersetCard σ m)).symm i) :=
  Module.Basis.reindex_apply (FrameFormBasis.frameBasis p k n A σ C ρ hρ hker hbase m)
    (Fintype.equivFin (Set.powersetCard σ m)) i

def linearEquiv (m : ℕ) : RelativeCrystalline.FreeModule.freeModule Q (Index m) F ≃ₗ[W]
    RelativeFrame.FormMap.frameModule (F).obj m :=
  (basis p k n A C σ ρ hρ hker hbase m).equivFun.symm.restrictScalars W

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameFreeModule
