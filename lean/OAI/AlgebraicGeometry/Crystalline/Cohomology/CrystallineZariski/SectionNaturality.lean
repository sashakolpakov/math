import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Image
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.RightKanEvaluation

/-! # Section Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.SectionNaturality.CrystallineZariskiSectionNaturality

noncomputable section

/-!
# Naturality of crystalline Zariski sections in the coefficient sheaf

Pointwise right Kan evaluation and the open-site equivalence give a
natural isomorphism with native global sections after open restriction.
This is the comparison needed on whole injective-resolution complexes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "Residual" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCover.CrystallineResidualCover.functor p k Y
local notation "Inclusion" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding.functor p k j
local notation "Fibre" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.KanFibre.CrystallineOpenKanFibre.functor p k j
local notation "Projection" => StructuredArrow.proj (op (Scheme.Hom.opensRange (Over.Hom.left j)))
  (Functor.op Residual)
local notation "NativeTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k Y
local notation "SmallTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "ZariskiTopology" => Opens.grothendieckTopology Y.left

abbrev projectionPrecomposition := (Functor.whiskeringLeft _ _ V).obj Projection

abbrev fibrePrecomposition := (Functor.whiskeringLeft _ _ V).obj Fibre

abbrev openPrecomposition := (Functor.whiskeringLeft _ _ V).obj (Inclusion).op

def diagramsIso : projectionPrecomposition p k j ⋙ fibrePrecomposition p k j ≅
    openPrecomposition p k j :=
  (Functor.whiskeringLeftObjCompIso Fibre Projection).symm ≪≫
    (Functor.whiskeringLeft _ _ V).mapIso (CrystallineOpen.KanFibre.CrystallineOpenKanFibre.projectionIso p k j)

def presheafIso : (Residual).op.ran ⋙
    (CategoryTheory.evaluation _ V).obj (op j.left.opensRange) ≅ openPrecomposition p k j ⋙ lim :=
  Module.RightKanEvaluation.ModuleRightKanEvaluation.iso (Site.CoefficientRing p k) (Residual).op (op j.left.opensRange) ≪≫
    Functor.isoWhiskerLeft (projectionPrecomposition p k j) (Functor.Initial.limIso Fibre).symm ≪≫
      (Functor.associator (projectionPrecomposition p k j) (fibrePrecomposition p k j) lim).symm ≪≫
        Functor.isoWhiskerRight (diagramsIso p k j) lim

abbrev evaluation : Sheaf NativeTopology V ⥤ V :=
  Image.CrystallineZariskiImage.functor p k Y ⋙ sheafToPresheaf ZariskiTopology V ⋙
    (CategoryTheory.evaluation _ V).obj (op j.left.opensRange)

def globalSectionsIso : CrystallineZariskiSectionNaturality.evaluation p k j ≅
    CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness.restriction p k j ⋙ Sheaf.Γ SmallTopology V :=
  Functor.isoWhiskerLeft (sheafToPresheaf NativeTopology V) (presheafIso p k j) ≪≫
    (Functor.isoWhiskerLeft (CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness.restriction p k j)
      (Sheaf.ΓNatIsoLim SmallTopology V)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.SectionNaturality.CrystallineZariskiSectionNaturality
