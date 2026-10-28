import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittAcyclicTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FiniteFreeFreeAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FreeYonedaAcyclicity

/-! # Witt Free Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFreeAcyclicity

noncomputable section

/-! The original smooth Witt frame terms are acyclic for sections at
every bounded object, via their actual finite free slice presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
variable (p : ℕ) [Fact p.Prime] (k A C σ : Type) [Field k] [CharP k p]
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
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf.Index σ
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

abbrev Cohomology (V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n) (m i : ℕ) := Abelian.Ext.{2}
  (Sheaf.freeYoneda (BoundedCrystalline.Site.topology f n) V (ModuleCat.of CR CR))
  ((Bounded.RelativeSheafComplex.complex f n F).X m) i

def cohomologyEquiv (V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n) (m i : ℕ) : Cohomology p k A C ρ hρ hker hbase n V m i ≃+
    Bounded.FiniteFreeFreeAcyclicity.Cohomology p k f n F V (Index m) i :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr CR (Iso.refl _)
    (WittAcyclicTerms.termIso p k A C σ ρ hρ hker hbase n m) i).toAddEquiv

include σ in
theorem positive_cohomology_zero (V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n) (m i : ℕ) :
    Subsingleton (Cohomology p k A C ρ hρ hker hbase n V m (i+1)) := by
  have := Bounded.FiniteFreeFreeAcyclicity.positive_cohomology_zero p k f n F V (Index m) i
  exact (cohomologyEquiv p k A C σ ρ hρ hker hbase n V m (i+1)).toEquiv.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFreeAcyclicity
