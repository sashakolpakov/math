import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricOpenSections

/-! # Open Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenSections

noncomputable section

/-!
# IntegralComparison: chart de Rham cohomology is realized in the original global incoming-section resolution
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  (g : (Crystalline.Presentation.affineScheme k C).left ⟶ Y) [Mono g]
  (hg : g ≫ fY = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) fY 0))

def map : DeRham.Comparison.deRhamComplex p k C ⟶
    BoundedOpen.Resolution.complex fY g 0 I :=
  GlobalSections.deRhamMap p k C σ g hg I ≫
    (Bounded.GeometricOpenSections.complexIso g hg 0 I).inv

instance map_quasiIso : QuasiIso (map p k C σ g hg I) := by
  dsimp only [map]
  infer_instance

def homologyIso (i : ℕ) : (DeRham.Comparison.deRhamComplex p k C).homology i ≅
    (BoundedOpen.Resolution.complex fY g 0 I).homology i := isoOfQuasiIsoAt (map p k C σ g hg I) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenSections
