import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameDeRhamIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameComplex

/-! # De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison

noncomputable section

/-! Original bounded crystalline Ext is computed by the ordinary de Rham complex of the constructed smooth Witt frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

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
local notation "CoeffW" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "An" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.Ring p A n

local instance frameAlgebra : Algebra W An := (FrameRing.base p k A n).toAlgebra

def coefficientFunctor : ModuleCat.{u} W ⥤ ModuleCat.{u + 2} CoeffW :=
  Crystalline.RelativeResolution.coefficientFunctor (B := W) ⋙ ModuleCat.uliftFunctor.{u + 2, u + 1} CoeffW

instance coefficientFunctor_additive : (coefficientFunctor p k).Additive := by
  dsimp [coefficientFunctor]
  infer_instance

def deRhamComplex : CochainComplex (ModuleCat.{u + 2} CoeffW) ℕ :=
  ((coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W An)

def frameIso : BoundedSmooth.WittFrameDeRhamIso.frameComplex p k A C ρ hρ hker hbase n ≅
    deRhamComplex p k A n :=
  ((coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (FrameComplex.frameIso p k A n C ρ hρ hker hbase)

def homologyIso (i : ℕ) : (deRhamComplex p k A n).homology i ≅
    ModuleCat.of CoeffW (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n i) :=
  ((HomologicalComplex.homologyFunctor _ _ i).mapIso (frameIso p k A C ρ hρ hker hbase n)).symm ≪≫
    BoundedSmooth.WittFrameDeRhamIso.homologyIso p k A C σ ρ hρ hker hbase n i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison
