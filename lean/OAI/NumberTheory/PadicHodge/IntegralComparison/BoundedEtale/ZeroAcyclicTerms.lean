import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.AmbientSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeImage

/-! # Zero Acyclic Terms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroAcyclicTerms

noncomputable section

/-!
# IntegralComparison: the actual étale zero-frame resolution has acyclic terms

Each term is identified with the native direct image of a finite free
module from the frame slice. Its positive cohomology therefore vanishes
in the original Ext cohomology theory restricted to the prescribed level.
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
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct.ambientPresheaf H
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage.directImage f 0 F
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f 0 F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf.Index σ

instance hasFiniteBiproducts : HasFiniteBiproducts (BoundedCrystalline.Site.ModuleSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def termIso (m : ℕ) : (K).X m ≅ (D).obj (Bounded.FiniteFreeImage.freeSheaf p k f 0 F (Index m)) :=
  (S).mapIso (ZeroFormPresheaf.biproductIso p k C σ m) ≪≫
    (S).mapBiproduct (fun _ : Index m => A) ≪≫
    biproduct.mapIso (fun _ : Index m => BoundedFrame.AmbientSheaf.sheafIso f 0 F) ≪≫
    ((D).mapBiproduct (Bounded.FiniteFreeImage.copies p k f 0 F (Index m))).symm

abbrev Cohomology (m i : ℕ) := Abelian.Ext.{u + 2} (BoundedCrystalline.CrystallineCohomology.constantUnit f 0) ((K).X m) i

def cohomologyEquiv (m i : ℕ) : Cohomology p k C m i ≃+
    Bounded.FiniteFreeImage.Cohomology p k f 0 F (Index m) i :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (Iso.refl _) (termIso p k C σ m) i).toAddEquiv

include σ in
theorem positive_cohomology_zero (m i : ℕ) : Subsingleton (Cohomology p k C m (i + 1)) := by
  have := Bounded.FiniteFreeImage.positive_cohomology_zero p k f 0 F (Index m) i
  exact (cohomologyEquiv p k C σ m (i + 1)).toEquiv.subsingleton

def degreeZeroEquiv (m : ℕ) : Cohomology p k C m 0 ≃+ (Index m → ULift.{u + 1} (F).obj.ring) :=
  (cohomologyEquiv p k C σ m 0).trans
    (Bounded.FiniteFreeImage.degreeZeroEquiv p k f 0 F (Index m))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroAcyclicTerms
