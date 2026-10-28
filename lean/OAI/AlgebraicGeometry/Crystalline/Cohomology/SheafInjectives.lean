import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedAdjunction
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Sheaf Injectives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives

noncomputable section

/-!
# Injective resolutions in the actual crystalline sheaf categories

The native and framed sites are essentially small at the universe of
their specified lifted Witt-module coefficients. Their sheaf categories
are therefore Grothendieck abelian categories and have enough injectives.
These are constructed categorical consequences, not cohomological inputs.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

abbrev Modules := ModuleCat.{u + 1} (Site.CoefficientRing p k)

instance nativeGrothendieck : IsGrothendieckAbelian.{u + 1}
    (Sheaf (Site.topology p k X) (Modules p k)) := by
  have : EssentiallySmall.{u + 1} (Site.Object p k X) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (Site.topology p k X) (Modules p k)

instance nativeEnoughInjectives : EnoughInjectives
    (Sheaf (Site.topology p k X) (Modules p k)) := inferInstance

variable (B σ : Type u) [CommRing B] [Algebra k B] (a : σ → B)

instance framedGrothendieck : IsGrothendieckAbelian.{u + 1}
    (Sheaf (FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a) (Modules p k)) := by
  have : EssentiallySmall.{u + 1} (FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a) (Modules p k)

instance framedEnoughInjectives : EnoughInjectives
    (Sheaf (FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a) (Modules p k)) := inferInstance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives
