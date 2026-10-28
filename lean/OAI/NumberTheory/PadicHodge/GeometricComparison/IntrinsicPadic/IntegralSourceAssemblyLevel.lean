import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSourceLevelMap

/-! # Integral Source Assembly Level -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceLevel

/-! Original integral quotient reductions commute with native frame
level maps after the actual crystalline coefficient functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "F" => Functor.mapHomologicalComplex (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p) (ComplexShape.up ℕ)

def transformation : IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X m ⟶
    IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X n :=
  Functor.whiskerRight (ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap.sourceTransition p X n m hnm) F

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem natural : IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp m ≫
    FrameSourceLevelMap.IntrinsicPadicFrameSourceLevelMap.transformation p X Y f hp n m hnm =
      transformation p X n m hnm ≫ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp n := by
  let G := (Functor.whiskeringRight X.left.affineOpensᵒᵖ
    (CochainComplex (ModuleCat (WittVector p (ZMod p))) ℕ)
      (CochainComplex (ModuleCat.{2} R) ℕ)).obj F
  exact (G.map_comp _ _).symm.trans
    ((congrArg G.map (ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap.pd p X Y f hp n m hnm)).trans (G.map_comp _ _))

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceLevel

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceAssemblyLevel

/-! The actual native integral quotient-to-frame comparison respects
level maps after assembling complexes of presheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X m) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X n) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntrinsicPadicIntegralSourceLevel.transformation p X n m hnm)

def frameMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp m) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp n) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (FrameSourceLevelMap.IntrinsicPadicFrameSourceLevelMap.transformation p X Y f hp n m hnm)

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem natural : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp m) ≫
    frameMap p X Y f hp n m hnm = IntrinsicPadicIntegralSourceAssemblyLevel.map p X n m hnm ≫
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp n) := by
  let A := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (T := X.left.affineOpensᵒᵖ)
    (V := ModuleCat.{2} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p)))) (.up ℕ)
  exact (A.map_comp _ _).symm.trans
    ((congrArg A.map (IntrinsicPadicIntegralSourceLevel.natural p X Y f hp n m hnm)).trans (A.map_comp _ _))

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceAssemblyLevel

end

end OAI
