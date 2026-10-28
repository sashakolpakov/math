import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ContinuousSheaf
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Sheaf Exactness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness.FramedCrystallineSheafExactness

noncomputable section

/-!
# Exact restriction to framed crystalline sheaves

Restriction along the forgetful functor preserves finite limits and
finite colimits. Its native frame right adjoint therefore preserves
injective objects. The results apply to the actual crystalline topology
and its specified Witt-vector module coefficients.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Limits

universe u v w

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (A : Type v) [Category.{w} A]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a

abbrev restriction : Sheaf J A ⥤ Sheaf K A :=
  (FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a).sheafPushforwardContinuous A K J

abbrev frame : Sheaf K A ⥤ Sheaf J A :=
  (FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a).sheafPushforwardContinuous A J K

instance restriction_finiteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (restriction p k B σ a A) :=
  ContinuousSheaf.ContinuousSheafLimits.preservesFiniteLimits _ _ _ _

instance restriction_finiteColimits : PreservesFiniteColimits (restriction p k B σ a A) := by
  have : (restriction p k B σ a A).IsLeftAdjoint :=
    (Topology.FramedCrystallineTopology.sheafAdjunction p k B σ a A J).isLeftAdjoint
  infer_instance

instance restriction_additive [Preadditive A] : (restriction p k B σ a A).Additive :=
  ContinuousSheaf.ContinuousSheafLimits.additive _ _ _ _

instance frame_additive [Preadditive A] : (frame p k B σ a A).Additive :=
  ContinuousSheaf.ContinuousSheafLimits.additive _ _ _ _

instance restriction_preservesHomology [Preadditive A] [HasFiniteLimits A] :
    (restriction p k B σ a A).PreservesHomology :=
  Functor.preservesHomologyOfExact _

instance frame_preservesInjectives [HasFiniteLimits A] :
    (frame p k B σ a A).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Topology.FramedCrystallineTopology.sheafAdjunction p k B σ a A J)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness.FramedCrystallineSheafExactness
