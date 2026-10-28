import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.KanFibre
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCocontinuity
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Sheaves
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Image -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Image.CrystallineZariskiImage

noncomputable section

/-!
# The native crystalline direct image on the Zariski site

Cocontinuity makes the actual right Kan extension a Zariski sheaf.
The proved open-site comma equivalence identifies its sections on each
open subscheme with native crystalline global sections on that open.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (Y : Over (Spec (CommRingCat.of k)))

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "Residual" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCover.CrystallineResidualCover.functor p k Y
local notation "NativeTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k Y
local notation "ZariskiTopology" => Opens.grothendieckTopology Y.left

abbrev functor : Sheaf NativeTopology V ⥤ Sheaf ZariskiTopology V :=
  (Residual).sheafPushforwardCocontinuous V NativeTopology ZariskiTopology

variable {Y} {X : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "Inclusion" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding.functor p k j
local notation "Fibre" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.KanFibre.CrystallineOpenKanFibre.functor p k j

def diagramIso (P : (Site.Object p k Y)ᵒᵖ ⥤ V) :
    Fibre ⋙ (StructuredArrow.proj (op j.left.opensRange) (Residual).op ⋙ P) ≅
      (Inclusion).op ⋙ P :=
  (Functor.associator Fibre (StructuredArrow.proj (op j.left.opensRange) (Residual).op) P).symm ≪≫
    Functor.isoWhiskerRight (CrystallineOpen.KanFibre.CrystallineOpenKanFibre.projectionIso p k j) P

def presheafSectionsIso (P : (Site.Object p k Y)ᵒᵖ ⥤ V) :
    ((Residual).op.ran.obj P).obj (op j.left.opensRange) ≅ limit ((Inclusion).op ⋙ P) :=
  (Residual).op.ranObjObjIsoLimit P (op j.left.opensRange) ≪≫
    (Functor.Initial.limitIso Fibre
      (StructuredArrow.proj (op j.left.opensRange) (Residual).op ⋙ P)).symm ≪≫
        HasLimit.isoOfNatIso (diagramIso p k j P)

def globalSectionsIso (F : Sheaf NativeTopology V) :
    ((functor p k Y).obj F).obj.obj (op j.left.opensRange) ≅
      (Sheaf.Γ (Site.topology p k X) V).obj
        ((CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness.restriction p k j).obj F) :=
  presheafSectionsIso p k j F.obj ≪≫
    ((Sheaf.ΓNatIsoLim (Site.topology p k X) V).app
      ((CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness.restriction p k j).obj F)).symm

def structureSectionsIso :
    ((functor p k Y).obj (Site.structureSheaf p k Y)).obj.obj (op j.left.opensRange) ≅
      (Sheaf.Γ (Site.topology p k X) V).obj (Site.structureSheaf p k X) :=
  globalSectionsIso p k j (Site.structureSheaf p k Y) ≪≫
    (Sheaf.Γ (Site.topology p k X) V).mapIso (CrystallineOpen.Sheaves.CrystallineOpenSheaves.structureIso p k j)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Image.CrystallineZariskiImage
