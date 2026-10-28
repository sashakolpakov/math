import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PresheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.InverseNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPrecomposition

/-! # Geometric Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GeometricSections

noncomputable section

/-! The original affine de Rham comparison respects geometric restriction on homology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C D σ τ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [CommRing D] [Algebra k C] [Algebra k D] [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  [Algebra (MvPolynomial τ k) D] [IsScalarTower k (MvPolynomial τ k) D] [Algebra.Etale (MvPolynomial τ k) D]
  (a : C →ₐ[k] D)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

variable [hmono : Mono (Zero.FrameGeometricMap.schemeMap k C D a)]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0))

def restriction : Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R
    (BoundedCrystalline.Site.topology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0) I.cocomplex ⟶
      Bounded.GeometricResolution.complex (Zero.FrameGeometricMap.schemeMap k C D a) (Zero.FrameGeometricMap.overWitt p k C D a) 0 I :=
  BoundedFrame.PresheafRestriction.restriction (Zero.FrameGeometricMap.schemeMap k C D a) (Zero.FrameGeometricMap.overWitt p k C D a) 0 I

theorem frame_homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (ResolutionSections.frameMap p k C σ I ≫ restriction p k C D a I) i =
    HomologicalComplex.homologyMap
      (ComplexMaps.frameMap p k C D a ≫ ResolutionSections.frameMap p k D τ (Bounded.GeometricResolution.resolution (Zero.FrameGeometricMap.schemeMap k C D a) (Zero.FrameGeometricMap.overWitt p k C D a) 0 I)) i := by
  let : QuasiIso (Bounded.RelativeSheafComplex.augmentation (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0 (ZeroLevel.LevelFrame.boundedFrame p k C)) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  let : QuasiIso (Bounded.RelativeSheafComplex.augmentation (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k D)) 0 (ZeroLevel.LevelFrame.boundedFrame p k D)) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k D τ
  exact (BoundedFrame.PresheafRestriction.homology (Zero.FrameGeometricMap.schemeMap k C D a) (Zero.FrameGeometricMap.overWitt p k C D a) 0 (ZeroLevel.LevelFrame.boundedFrame p k C) I (ZeroLevel.LevelFrame.boundedFrame p k D)
    (Zero.FrameGeometricMap.boundedMap p k C D a) i).trans
      (congrArg (fun b => HomologicalComplex.homologyMap
        (b ≫ ResolutionSections.frameMap p k D τ (Bounded.GeometricResolution.resolution (Zero.FrameGeometricMap.schemeMap k C D a) (Zero.FrameGeometricMap.overWitt p k C D a) 0 I)) i)
          (Zero.FrameGeometricMap.frameMap p k C D a))

theorem deRham_homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (ResolutionSections.map p k C σ I ≫ restriction p k C D a I) i =
    HomologicalComplex.homologyMap
      (ComplexMaps.deRhamMap p k C D a ≫ ResolutionSections.map p k D τ (Bounded.GeometricResolution.resolution (Zero.FrameGeometricMap.schemeMap k C D a) (Zero.FrameGeometricMap.overWitt p k C D a) 0 I)) i := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 2} R) (.up ℕ) i
  let c := (DeRham.Comparison.frameIso p k C).inv
  let d := ResolutionSections.frameMap p k D τ (Bounded.GeometricResolution.resolution (Zero.FrameGeometricMap.schemeMap k C D a) (Zero.FrameGeometricMap.overWitt p k C D a) 0 I)
  exact (congrArg H.map (Category.assoc c (ResolutionSections.frameMap p k C σ I)
    (restriction p k C D a I))).trans
      ((HomologyMapPrecomposition.equality c _ _ i (frame_homology p k C D σ τ a I i)).trans
        ((congrArg H.map (Category.assoc c (ComplexMaps.frameMap p k C D a) d).symm).trans
          ((congrArg (fun b => H.map (b ≫ d)) (InverseNaturality.map p k C D a)).trans
            (congrArg H.map (Category.assoc _ _ _)))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GeometricSections
