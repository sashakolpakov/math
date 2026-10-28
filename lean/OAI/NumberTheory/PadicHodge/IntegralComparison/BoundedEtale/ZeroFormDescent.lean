import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroAcyclicTerms

/-! # Zero Form Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormDescent

noncomputable section

/-!
# IntegralComparison: the canonical relative form presheaves already satisfy bounded descent
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct.ambientPresheaf H
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.coefficientPresheaves (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf.Index σ
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def presheafIso (m : ℕ) :
    (L).obj (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) ≅
      (⨁ (fun _ : Index m => BoundedFrame.AmbientSheaf.ambientSheaf f 0 F)).obj :=
  (L).mapIso (ZeroFormPresheaf.biproductIso p k C σ m) ≪≫
    (L).mapBiproduct (fun _ : Index m => A) ≪≫
    biproduct.mapIso (fun _ : Index m => BoundedFrame.AmbientSheaf.presheafIso f 0 F) ≪≫
    ((sheafToPresheaf (BoundedCrystalline.Site.topology f 0) (ModuleCat.{u + 1} R)).mapBiproduct
      (fun _ : Index m => BoundedFrame.AmbientSheaf.ambientSheaf f 0 F)).symm

include σ in
theorem isSheaf (m : ℕ) : Presheaf.IsSheaf (BoundedCrystalline.Site.topology f 0)
    ((L).obj (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)) :=
  (Presheaf.isSheaf_of_iso_iff (presheafIso p k C σ m)).mpr
    (⨁ (fun _ : Index m => BoundedFrame.AmbientSheaf.ambientSheaf f 0 F)).property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormDescent
