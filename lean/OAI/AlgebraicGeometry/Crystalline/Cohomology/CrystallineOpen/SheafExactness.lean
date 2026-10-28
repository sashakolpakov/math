import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Topology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ContinuousSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Sheaf Exactness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness

noncomputable section

/-! # Exact restriction of native crystalline module sheaves to open subschemes -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "Inclusion" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding.functor p k j
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "SmallTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "LargeTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k Y

abbrev restriction : Sheaf LargeTopology V ⥤ Sheaf SmallTopology V :=
  (Inclusion).sheafPushforwardContinuous V SmallTopology LargeTopology

instance finiteLimits : PreservesFiniteLimits (restriction p k j) :=
  ContinuousSheaf.ContinuousSheafLimits.preservesFiniteLimits _ _ _ _

instance finiteColimits : PreservesFiniteColimits (restriction p k j) := by
  have : (restriction p k j).IsLeftAdjoint :=
    ((Inclusion).sheafAdjunctionCocontinuous V SmallTopology LargeTopology).isLeftAdjoint
  infer_instance

instance additive : (restriction p k j).Additive :=
  ContinuousSheaf.ContinuousSheafLimits.additive _ _ _ _

instance linear : (restriction p k j).Linear (Site.CoefficientRing p k) where
  map_smul := by intros; rfl

instance preservesHomology : (restriction p k j).PreservesHomology :=
  Functor.preservesHomologyOfExact _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness
