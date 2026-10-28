import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Cocontinuity
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution

/-! # Sheaf Pushforward -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward

noncomputable section

/-!
# Exact native frame pushforward and its structure-sheaf comparison

Full cover lifting makes the native frame pushforward exact. Its
commutation with sheafification identifies the actual sheafified frame
functions with the frame restriction of the original structure sheaf.
The isomorphism is the canonical sheafification comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a

abbrev Coefficients := ModuleCat.{u + 1} (Site.CoefficientRing p k)

def frameForgetIso : G ⋙ U ≅ F := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

instance continuous : (F).IsContinuous J J := by
  have : (G ⋙ U).IsContinuous J J := Functor.isContinuous_comp G U J K J
  exact Functor.isContinuous_of_iso (frameForgetIso p k B σ a) J J

instance cocontinuous : (F).IsCocontinuous J J := by
  have : (G ⋙ U).IsCocontinuous J J := isCocontinuous_comp G U J K
  exact Functor.IsCocontinuous.of_iso (frameForgetIso p k B σ a)

abbrev pushforward : Sheaf J (Coefficients p k) ⥤ Sheaf J (Coefficients p k) :=
  (F).sheafPushforwardContinuous (Coefficients p k) J J

instance preservesFiniteLimits : PreservesFiniteLimits (pushforward p k B σ a) :=
  ContinuousSheaf.ContinuousSheafLimits.preservesFiniteLimits _ _ _ _

instance preservesFiniteColimits : PreservesFiniteColimits (pushforward p k B σ a) := by
  have : (pushforward p k B σ a).IsLeftAdjoint :=
    ((F).sheafAdjunctionCocontinuous (Coefficients p k) J J).isLeftAdjoint
  infer_instance

instance additive : (pushforward p k B σ a).Additive := ContinuousSheaf.ContinuousSheafLimits.additive _ _ _ _

instance preservesHomology : (pushforward p k B σ a).PreservesHomology :=
  Functor.preservesHomologyOfExact _

def structureSheafIso :
    (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).obj
      (Operators.CrystallineFrameOperators.functions p k B σ a) ≅
      (pushforward p k B σ a).obj (Site.structureSheaf p k X) :=
  ((F).pushforwardContinuousSheafificationCompatibility (Coefficients p k) J J).app
    (Site.functionsLarge p k X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward
