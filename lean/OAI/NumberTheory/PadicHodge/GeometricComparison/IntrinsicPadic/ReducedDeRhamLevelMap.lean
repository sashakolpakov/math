import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReductionLevelSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamLevel
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Reduced De Rham Level Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap

noncomputable section

/-! The actual native integral coefficient-quotient comparisons commute
with prime-power level transitions into ordinary and PD frame diagrams. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "In" => (Ideal.span {(p : W)}) ^ (n + 1)
local notation "Im" => (Ideal.span {(p : W)}) ^ (m + 1)

def sourceTransition : ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X m ⟶ ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n :=
  Functor.whiskerLeft (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W)
    ((IntegralComparison.Module.IdealQuotientTransition.transformation W Im In
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))).mapHomologicalComplex (.up ℕ))

theorem ordinary : ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X Y f hp m ≫
    FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.ordinary p X Y f hp n m hnm =
      sourceTransition p X n m hnm ≫ ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X Y f hp n := by
  apply NatTrans.ext
  funext I
  exact OrdinaryDeRhamLevel.OrdinaryDeRhamReductionLevel.natural W Im In (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))
    ((QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp m).app I)
    ((QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n).app I)
    ((FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.rings p X Y f hp n m hnm).app I)
    (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X Y f hp m I)
    (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X Y f hp n I)
    (ReductionLevelSquare.IntrinsicPadicReductionLevelSquare.component p X Y f hp n m hnm I.unop)

theorem inverse_comparison : FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.ordinary p X Y f hp n m hnm ≫
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp n).inv =
      (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp m).inv ≫
        FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.pd p X Y f hp n m hnm :=
  IntegralComparison.InverseCoordinateHomology.inverse (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp m)
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp n)
    (FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.pd p X Y f hp n m hnm)
    (FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.ordinary p X Y f hp n m hnm)
    (FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.pd_ordinary p X Y f hp n m hnm)

theorem pd : ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X Y f hp m ≫
    FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.pd p X Y f hp n m hnm =
      sourceTransition p X n m hnm ≫ ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X Y f hp n :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun a => ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X Y f hp m ≫ a)
      (inverse_comparison p X Y f hp n m hnm).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp n).inv)
            (ordinary p X Y f hp n m hnm)).trans (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap
