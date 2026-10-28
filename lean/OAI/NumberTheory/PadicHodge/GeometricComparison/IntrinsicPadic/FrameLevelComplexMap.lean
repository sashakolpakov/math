import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelUnderlyingDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameNaturality

/-! # Frame Level Complex Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap

noncomputable section

/-! Actual native frame reductions induce natural maps on their ring,
ordinary de Rham and PD de Rham diagrams, with the original comparison square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "frame" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp

def frames : PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp m ⟶
    PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp n :=
  Bounded.LevelUnderlyingDiagram.BoundedLevelUnderlyingDiagram.opTransformation wittMap n m hnm (frame n) (frame m)
    (FrameLevelNaturality.IntrinsicPadicFrameLevelNaturality.transformation p X Y f hp n m hnm)

def rings : PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X Y f hp m ⟶
    PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X Y f hp n :=
  Functor.whiskerRight (frames p X Y f hp n m hnm) (Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.functor wittMap)

def ordinary : PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ordinaryComplexes p X Y f hp m ⟶
    PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ordinaryComplexes p X Y f hp n :=
  Functor.whiskerRight (rings p X Y f hp n m hnm) (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W)

def pd : PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp m ⟶
    PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n :=
  Functor.whiskerRight (frames p X Y f hp n m hnm) (Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor wittMap)

theorem pd_ordinary : pd p X Y f hp n m hnm ≫ (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp n).hom =
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp m).hom ≫ ordinary p X Y f hp n m hnm :=
  PrincipalFrameNaturality.PrincipalFrameComparisonNaturality.natural (p : W) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp m)
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp n)
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ideal_generated p X Y f hp m)
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ideal_generated p X Y f hp n)
    (frames p X Y f hp n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap
