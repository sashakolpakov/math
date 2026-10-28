import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Injective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroResolution

/-! # To Global Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ToGlobalResolution

noncomputable section

/-!
# IntegralComparison: the original étale zero-frame resolution maps into the restricted global injective resolution
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  (g : (Crystalline.Presentation.affineScheme k C).left ⟶ Y) [Mono g]
  (hg : g ≫ fY = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) fY 0))

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution g hg 0 I

def map : Bounded.RelativeSheafComplex.complex f 0 F ⟶ (IX).cocomplex := by
  letI : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact BoundedFrame.Injective.Comparison.map f 0 F IX

theorem augmentation : Bounded.RelativeSheafComplex.augmentation f 0 F ≫ map p k C σ g hg I = (IX).ι := by
  let : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact BoundedFrame.Injective.Comparison.augmentation f 0 F IX

instance map_quasiIso : QuasiIso (map p k C σ g hg I) := by
  let : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact BoundedFrame.Injective.Comparison.map_quasiIso f 0 F IX

def homotopy (a : Bounded.RelativeSheafComplex.complex f 0 F ⟶ (IX).cocomplex)
    (ha : Bounded.RelativeSheafComplex.augmentation f 0 F ≫ a = (IX).ι) :
    Homotopy (map p k C σ g hg I) a := by
  letI : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact BoundedFrame.Injective.Comparison.homotopy f 0 F IX a ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ToGlobalResolution
