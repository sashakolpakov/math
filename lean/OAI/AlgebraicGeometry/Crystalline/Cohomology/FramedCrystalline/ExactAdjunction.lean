import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward

/-! # Exact Adjunction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction

noncomputable section

/-!
# Exactness on both sides of the native framed-sheaf adjunction

The frame functor's full cover lifting proves exactness of the right
adjoint on the actual Witt-module sheaf categories. The existing native
frame functions are identified with this right adjoint applied to the
restriction of the original structure sheaf.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.Coefficients p k
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a

abbrev restriction := SheafExactness.FramedCrystallineSheafExactness.restriction p k B σ a V
abbrev frame := SheafExactness.FramedCrystallineSheafExactness.frame p k B σ a V

instance frame_finiteLimits : PreservesFiniteLimits (frame p k B σ a) :=
  ContinuousSheaf.ContinuousSheafLimits.preservesFiniteLimits _ _ _ _

instance frame_finiteColimits : PreservesFiniteColimits (frame p k B σ a) := by
  have : (frame p k B σ a).IsLeftAdjoint :=
    ((G).sheafAdjunctionCocontinuous V J K).isLeftAdjoint
  infer_instance

instance frame_preservesHomology : (frame p k B σ a).PreservesHomology :=
  Functor.preservesHomologyOfExact _

def structureSheafIso :
    (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).obj
      (CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a) ≅
      (frame p k B σ a).obj ((restriction p k B σ a).obj (Site.structureSheaf p k X)) :=
  CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.structureSheafIso p k B σ a ≪≫
    ((Functor.sheafPushforwardContinuousComp'
      (CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.frameForgetIso p k B σ a) V J K J).app
        (Site.structureSheaf p k X)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction
