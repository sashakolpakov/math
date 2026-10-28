import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittAcyclicTerms

/-! # Witt Form Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormDescent

noncomputable section

/-!
# IntegralComparison: the canonical relative form presheaves already satisfy bounded descent
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "AP" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct.ambientPresheaf H
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.coefficientPresheaves (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf.Index σ
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def presheafIso (m : ℕ) :
    (L).obj (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) ≅
      (⨁ (fun _ : Index m => BoundedFrame.AmbientSheaf.ambientSheaf f n F)).obj :=
  (L).mapIso (WittFormPresheaf.biproductIso p k A C σ ρ hρ hker hbase n m) ≪≫
    (L).mapBiproduct (fun _ : Index m => AP) ≪≫
    biproduct.mapIso (fun _ : Index m => BoundedFrame.AmbientSheaf.presheafIso f n F) ≪≫
    ((sheafToPresheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} R)).mapBiproduct
      (fun _ : Index m => BoundedFrame.AmbientSheaf.ambientSheaf f n F)).symm

include σ in
theorem isSheaf (m : ℕ) : Presheaf.IsSheaf (BoundedCrystalline.Site.topology f n)
    ((L).obj (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)) :=
  (Presheaf.isSheaf_of_iso_iff (presheafIso p k A C σ ρ hρ hker hbase n m)).mpr
    (⨁ (fun _ : Index m => BoundedFrame.AmbientSheaf.ambientSheaf f n F)).property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormDescent
