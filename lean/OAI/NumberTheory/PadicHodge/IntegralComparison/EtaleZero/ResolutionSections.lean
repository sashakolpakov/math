import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.Presheaf

/-! # Resolution Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionSections

noncomputable section

/-! The existing affine comparison expressed for its actual chosen injective resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def frameMap (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0)) :
    BoundedEtale.ZeroFrameDeRhamIso.frameComplex p k C ⟶
      Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R
        (BoundedCrystalline.Site.topology f 0) I.cocomplex := by
  letI : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact BoundedFrame.Presheaf.Comparison.map f 0 F I

def map (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0)) :
    DeRham.Comparison.deRhamComplex p k C ⟶
      Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R
        (BoundedCrystalline.Site.topology f 0) I.cocomplex :=
  (DeRham.Comparison.frameIso p k C).inv ≫ frameMap p k C σ I

variable {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  (g : (Crystalline.Presentation.affineScheme k C).left ⟶ Y) [Mono g]
  (hg : g ≫ fY = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) fY 0))

omit [LinearOrder σ] in
theorem restricted_frameMap : frameMap p k C σ (Bounded.GeometricResolution.resolution g hg 0 I) =
    Presheaf.Comparison.frameMap p k C σ g hg I := rfl

theorem restricted : map p k C σ (Bounded.GeometricResolution.resolution g hg 0 I) =
    GlobalSections.deRhamMap p k C σ g hg I :=
  (Presheaf.Comparison.deRhamMap_eq p k C σ g hg I).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionSections
