import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Presheaf

/-! # Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.Presheaf.Comparison

noncomputable section

/-! The original affine de Rham comparison is the canonical frame comparison in presheaf coordinates. -/

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

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution g hg 0 I

def frameMap : BoundedEtale.ZeroFrameDeRhamIso.frameComplex p k C ⟶
    Bounded.GeometricResolution.complex g hg 0 I := by
  letI : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact BoundedFrame.Presheaf.Comparison.map f 0 F IX

theorem frameMap_component (i : ℕ) : (frameMap p k C σ g hg I).f i =
    (BoundedEtale.ZeroFrameDeRhamIso.complexIso p k C σ).hom.f i ≫
      (GlobalSections.map p k C σ g hg I).f i ≫
        (GlobalSections.sectionIso p k C g hg I).hom.f i := by
  let : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact BoundedFrame.Presheaf.Comparison.factorization_component f 0 F IX i

theorem frameMap_eq : frameMap p k C σ g hg I =
    (BoundedEtale.ZeroFrameDeRhamIso.complexIso p k C σ).hom ≫
      GlobalSections.presheafMap p k C σ g hg I := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact frameMap_component p k C σ g hg I i

theorem deRhamMap_eq : GlobalSections.deRhamMap p k C σ g hg I =
    (DeRham.Comparison.frameIso p k C).inv ≫ frameMap p k C σ g hg I :=
  congrArg (fun a => (DeRham.Comparison.frameIso p k C).inv ≫ a)
    (frameMap_eq p k C σ g hg I).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.Presheaf.Comparison
