import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GeometricSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionMapCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionCongr
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.TwoStage

/-! # Global Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalRestriction

noncomputable section

/-! Original affine comparisons commute on homology after restricting one global crystalline resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C D σ τ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [CommRing D] [Algebra k C] [Algebra k D] [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  [Algebra (MvPolynomial τ k) D] [IsScalarTower k (MvPolynomial τ k) D] [Algebra.Etale (MvPolynomial τ k) D]
  (a : C →ₐ[k] D)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

variable [hmono : Mono (Zero.FrameGeometricMap.schemeMap k C D a)] {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  (c : (Crystalline.Presentation.affineScheme k C).left ⟶ Y) (d : (Crystalline.Presentation.affineScheme k D).left ⟶ Y) [Mono c] [Mono d]
  (hC : c ≫ fY = (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C))) (hD : d ≫ fY = (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k D))) (e : (Zero.FrameGeometricMap.schemeMap k C D a) ≫ c = d)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) fY 0))

local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition.overBase (OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap.schemeMap k C D a) c (OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap.overWitt p k C D a) hC
local notation "IC" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution c hC 0 I
local notation "IN" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution (OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap.schemeMap k C D a) (OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap.overWitt p k C D a) 0 IC
local notation "IM" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution ((OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap.schemeMap k C D a) ≫ c) hc 0 I
local notation "ID" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution d hD 0 I

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (ResolutionSections.map p k C σ IC ≫
        GeometricSections.restriction p k C D a IC ≫
          ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R
            (BoundedCrystalline.Site.topology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k D)) 0)).mapHomologicalComplex (.up ℕ)).map
              (Bounded.ResolutionComposition.iso (Zero.FrameGeometricMap.schemeMap k C D a) c (Zero.FrameGeometricMap.overWitt p k C D a) hC 0 I).hom ≫
          ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R
            (BoundedCrystalline.Site.topology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k D)) 0)).mapHomologicalComplex (.up ℕ)).map
              (Bounded.ResolutionCongr.iso ((Zero.FrameGeometricMap.schemeMap k C D a) ≫ c) d hc hD e 0 I).hom) i =
    HomologicalComplex.homologyMap
      (ComplexMaps.deRhamMap p k C D a ≫ ResolutionSections.map p k D τ ID) i :=
  Functor.TwoStage.Comparison.transport
    (HomologicalComplex.homologyFunctor (ModuleCat.{u + 2} R) (.up ℕ) i)
    (ResolutionSections.map p k C σ IC)
    (GeometricSections.restriction p k C D a IC)
    (ComplexMaps.deRhamMap p k C D a)
    (ResolutionSections.map p k D τ IN)
    (ResolutionSections.map p k D τ IM)
    (ResolutionSections.map p k D τ ID) _ _
    (GeometricSections.deRham_homology p k C D σ τ a IC i)
    (ResolutionMapCoherence.deRham_homology p k D τ IN IM
      (Bounded.ResolutionComposition.iso (Zero.FrameGeometricMap.schemeMap k C D a) c (Zero.FrameGeometricMap.overWitt p k C D a) hC 0 I).hom
      (Bounded.ResolutionComposition.augmentation (Zero.FrameGeometricMap.schemeMap k C D a) c (Zero.FrameGeometricMap.overWitt p k C D a) hC 0 I) i)
    (ResolutionMapCoherence.deRham_homology p k D τ IM ID
      (Bounded.ResolutionCongr.iso ((Zero.FrameGeometricMap.schemeMap k C D a) ≫ c) d hc hD e 0 I).hom
      (Bounded.ResolutionCongr.augmentation ((Zero.FrameGeometricMap.schemeMap k C D a) ≫ c) d hc hD e 0 I) i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalRestriction
