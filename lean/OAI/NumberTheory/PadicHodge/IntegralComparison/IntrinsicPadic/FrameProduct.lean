import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameCohomologyProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientCohomologyCup

/-! # Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProduct.IntrinsicRaw

noncomputable section

/-! The original Witt-valued frame Čech cohomology maps to the
original bounded crystalline groups with their balanced cup product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.complex p X Y f hp n
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.cup p X Y f hp n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev coefficient (i : ℕ) := Crystalline.CoefficientCohomologyCup.map W M i

def map (i : ℕ) :=
  (FrameCohomologyProduct.Intrinsic.comparison p X Y f hp n i).toAddMonoidHom.comp
    (coefficient p X Y f hp n i)

omit [IsSeparated Y.hom] in
theorem coefficient_cup (i j : ℕ) (x : (M).homology i) (y : (M).homology j) :
    coefficient p X Y f hp n (i+j) (Frame.DiagramProduct.cohomologyCup w H U i j x y) =
      FrameCohomologyProduct.Intrinsic.cup p X Y f hp n i j
        (coefficient p X Y f hp n i x) (coefficient p X Y f hp n j y) :=
  Crystalline.CoefficientCohomologyCup.map_cup W M μ
    (Frame.DiagramProduct.differential_cup w H U) i j x y

attribute [local irreducible] FrameCohomologyProduct.Intrinsic.cup

theorem map_cup (i j : ℕ) (x : (M).homology i) (y : (M).homology j) :
    IntrinsicRaw.map p X Y f hp n (i+j) (Frame.DiagramProduct.cohomologyCup w H U i j x y) =
      BalancedBounded.CechCup.cup p (ZMod p) w n
        (BoundedCech.IntrinsicComparison.frames p X Y f hp n)
        (GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n) i j
        (IntrinsicRaw.map p X Y f hp n i x) (IntrinsicRaw.map p X Y f hp n j y) := by
  exact (congrArg
    (FrameCohomologyProduct.Intrinsic.comparison p X Y f hp n (i+j))
    (coefficient_cup p X Y f hp n i j x y)).trans
    (FrameCohomologyProduct.Intrinsic.comparison_cup p X Y f hp n i j _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProduct.IntrinsicRaw
