import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameChartMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ComplexMaps

/-! # Frame Geometric Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap

noncomputable section

/-! Native algebra restriction gives the actual geometric map of zeroth-level crystalline frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) [Fact p.Prime] (k C D : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [CommRing D] [Algebra k C] [Algebra k D] (f : C →ₐ[k] D)

def schemeMap := FrameChartMap.schemeMap k C D f

omit [Fintype k] [CharP k p] in
theorem overWitt : schemeMap k C D f ≫ Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C) =
    Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k D) :=
  Crystalline.OpenPresentation.overWitt p k D (Crystalline.Presentation.affineScheme k C) (schemeMap k C D f)
    (FrameChartMap.schemeMap_over k C D f)

def map : (BigCrystallineSite.postcompose (schemeMap k C D f) (overWitt p k C D f)).obj (ZeroLevel.LevelFrame.frame p k D) ⟶
    ZeroLevel.LevelFrame.frame p k C where
  ringMap := IdealPDMap.map (dividedPowersBot D) f.toRingHom
  overBase := RingHom.ext (fun w => f.commutes (WittVector.constantCoeff w))
  overX := FrameChartMap.quotientSquare k C D f

def boundedMap :
    (BoundedOpen.Equivalence.postcompose (schemeMap k C D f) (overWitt p k C D f) 0).obj
      (ZeroLevel.LevelFrame.boundedFrame p k D) ⟶ ZeroLevel.LevelFrame.boundedFrame p k C :=
  ObjectProperty.homMk (FrameGeometricMap.map p k C D f)

omit [Fintype k] in
theorem frameMap :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))).mapHomologicalComplex
      (.up ℕ)).map (BoundedFrame.SectionChange.frameMap (boundedMap p k C D f)) =
        EtaleZero.ComplexMaps.frameMap p k C D f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameGeometricMap
