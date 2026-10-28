import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Injectives

/-! # Sheaves -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Sheaves.CrystallineOpenSheaves

noncomputable section

/-!
# The original crystalline coefficient and structure sheaves restrict canonically

Restriction commutes with sheafification, and its underlying PD-ring
presheaf is unchanged. Thus both defining sheaves of the original
crystalline Ext groups restrict to their actual counterparts on the open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "Inclusion" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding.functor p k j
local notation "Restriction" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness.restriction p k j
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "SmallTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "LargeTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k Y

def coefficientIso : (Restriction).obj (Site.coefficientSheaf p k Y) ≅
    Site.coefficientSheaf p k X :=
  (((Inclusion).pushforwardContinuousSheafificationCompatibility V SmallTopology LargeTopology).app
    ((Functor.const (Site.Object p k Y)ᵒᵖ).obj
      (ModuleCat.of (Site.CoefficientRing p k) (Site.CoefficientRing p k)))).symm

def functionsLargeIso : (Inclusion).op ⋙ Site.functionsLarge p k Y ≅
    Site.functionsLarge p k X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

def structureIso : (Restriction).obj (Site.structureSheaf p k Y) ≅
    Site.structureSheaf p k X :=
  (((Inclusion).pushforwardContinuousSheafificationCompatibility V SmallTopology LargeTopology).app
    (Site.functionsLarge p k Y)).symm ≪≫
      (presheafToSheaf SmallTopology V).mapIso (functionsLargeIso p k j)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Sheaves.CrystallineOpenSheaves
