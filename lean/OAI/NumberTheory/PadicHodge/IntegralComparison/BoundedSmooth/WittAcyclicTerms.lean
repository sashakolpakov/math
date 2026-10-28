import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.AmbientSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeImage

/-! # Witt Acyclic Terms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittAcyclicTerms

noncomputable section

/-!
# IntegralComparison: the actual smooth Witt frame resolution has acyclic terms

Each term is identified with the native direct image of a finite free
module from the frame slice. Its positive cohomology therefore vanishes
in the original Ext cohomology theory restricted to the prescribed bounded Witt level.
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
local notation "AP" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct.ambientPresheaf H
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage.directImage f n F
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf.Index σ

instance hasFiniteBiproducts : HasFiniteBiproducts (BoundedCrystalline.Site.ModuleSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def termIso (m : ℕ) : (K).X m ≅ (D).obj (Bounded.FiniteFreeImage.freeSheaf p k f n F (Index m)) :=
  (S).mapIso (WittFormPresheaf.biproductIso p k A C σ ρ hρ hker hbase n m) ≪≫
    (S).mapBiproduct (fun _ : Index m => AP) ≪≫
    biproduct.mapIso (fun _ : Index m => BoundedFrame.AmbientSheaf.sheafIso f n F) ≪≫
    ((D).mapBiproduct (Bounded.FiniteFreeImage.copies p k f n F (Index m))).symm

abbrev Cohomology (m i : ℕ) := Abelian.Ext.{u + 2} (BoundedCrystalline.CrystallineCohomology.constantUnit f n) ((K).X m) i

def cohomologyEquiv (m i : ℕ) : Cohomology p k A C ρ hρ hker hbase n m i ≃+
    Bounded.FiniteFreeImage.Cohomology p k f n F (Index m) i :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (Iso.refl _) (termIso p k A C σ ρ hρ hker hbase n m) i).toAddEquiv

include σ in
theorem positive_cohomology_zero (m i : ℕ) : Subsingleton (Cohomology p k A C ρ hρ hker hbase n m (i + 1)) := by
  have := Bounded.FiniteFreeImage.positive_cohomology_zero p k f n F (Index m) i
  exact (cohomologyEquiv p k A C σ ρ hρ hker hbase n m (i + 1)).toEquiv.subsingleton

def degreeZeroEquiv (m : ℕ) : Cohomology p k A C ρ hρ hker hbase n m 0 ≃+ (Index m → ULift.{u + 1} (F).obj.ring) :=
  (cohomologyEquiv p k A C σ ρ hρ hker hbase n m 0).trans
    (Bounded.FiniteFreeImage.degreeZeroEquiv p k f n F (Index m))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittAcyclicTerms
