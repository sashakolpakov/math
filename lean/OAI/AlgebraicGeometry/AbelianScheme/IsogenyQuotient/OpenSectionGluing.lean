import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenPullbackMapGluing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSectionSquares
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BasisPullbackMapGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

/-! # Open Section Gluing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenSectionGluing.Construction

noncomputable section

/-! Glue actual local sections using the canonical pullback refinements.
The recovery equation is equality of sections, including the unit maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

universe u v
variable {X Y Z : Scheme.{u}} {M : Z.Modules}

def refineSectionTo (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj M) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback k).obj M :=
  AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullbackComp f g).hom.app M ≫
    (Scheme.Modules.pullbackCongr h).hom.app M

theorem refinePullbackMapTo_section (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj M) :
    OpenPullbackMapGluing.Construction.refinePullbackMapTo f g k h ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫ s) =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso k).hom ≫ refineSectionTo f g k h s := by
  subst k
  have hu := congrArg (fun a => a ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv)
    (Picard.PoincareBundle.StructureUnitComposition.unitIso_comp_inv f g)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hu
  change (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom =
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv at hu
  simp only [OpenPullbackMapGluing.Construction.refinePullbackMapTo, refineSectionTo, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id,
    AbelianModuli.HilbertConstruction.OpenPullback.Refinement.refineOpenPullbackMap, Functor.map_comp, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection]
  simp only [← Category.assoc]
  rw [hu]

theorem existsUnique_section_of_refinement_compatibility {ι : Type v}
    (U : ι → Z.Opens) (hU : ∀ z : Z, ∃ i, z ∈ U i)
    (s : ∀ i, AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U i).toScheme ⟶ (Scheme.Modules.pullback (U i).ι).obj M)
    (hs : ∀ i j (V : Z.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      refineSectionTo (Z.homOfLE hi) (U i).ι V.ι (Z.homOfLE_ι hi) (s i) =
        refineSectionTo (Z.homOfLE hj) (U j).ι V.ι (Z.homOfLE_ι hj) (s j)) :
    ∃! a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ⟶ M, ∀ i, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U i).ι a = s i := by
  have hmaps : ∀ i j (V : Z.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      OpenPullbackMapGluing.Construction.refinePullbackMapTo (Z.homOfLE hi) (U i).ι V.ι (Z.homOfLE_ι hi)
          ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U i).ι).hom ≫ s i) =
        OpenPullbackMapGluing.Construction.refinePullbackMapTo (Z.homOfLE hj) (U j).ι V.ι (Z.homOfLE_ι hj)
          ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U j).ι).hom ≫ s j) := by
    intro i j V hi hj
    rw [refinePullbackMapTo_section, refinePullbackMapTo_section, hs i j V hi hj]
  obtain ⟨a, ha, hu⟩ := OpenPullbackMapGluing.Construction.existsUnique_hom_of_refinement_compatibility U hU
    (fun i => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U i).ι).hom ≫ s i) hmaps
  refine ⟨a, ?_, ?_⟩
  · intro i
    exact (congrArg (fun b => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U i).ι).inv ≫ b) (ha i)).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U i).ι).inv_hom_id_assoc (s i))
  · intro a' ha'
    apply hu
    intro i
    have h := congrArg (fun b => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U i).ι).hom ≫ b) (ha' i)
    simpa only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Iso.hom_inv_id_assoc] using h

theorem existsUnique_section_of_basis_refinements {ι : Type v}
    (B : ι → Z.Opens) (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (s : ∀ i, AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (B i).toScheme ⟶ (Scheme.Modules.pullback (B i).ι).obj M)
    (hs : ∀ i j (h : B i ≤ B j),
      refineSectionTo (Z.homOfLE h) (B j).ι (B i).ι (Z.homOfLE_ι h) (s j) = s i) :
    ∃! a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ⟶ M, ∀ i, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (B i).ι a = s i := by
  let maps i := (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (B i).ι).hom ≫ s i
  have hmaps : ∀ i j (h : B i ≤ B j),
      OpenPullbackMapGluing.Construction.refinePullbackMapTo (Z.homOfLE h) (B j).ι (B i).ι (Z.homOfLE_ι h) (maps j) = maps i := by
    intro i j h
    exact (refinePullbackMapTo_section (Z.homOfLE h) (B j).ι (B i).ι
      (Z.homOfLE_ι h) (s j)).trans
      (congrArg (fun a => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (B i).ι).hom ≫ a) (hs i j h))
  let a := (BasisPullbackMapGluing.Construction.compatibleBasisPullbackMaps B maps hmaps).extend hB
  have ha i : (Scheme.Modules.pullback (B i).ι).map a = maps i :=
    BasisPullbackMapGluing.Construction.basisPullbackMaps_extend_pullback B hB maps hmaps i
  refine ⟨a, ?_, ?_⟩
  · intro i
    exact (congrArg (fun b => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (B i).ι).inv ≫ b) (ha i)).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (B i).ι).inv_hom_id_assoc (s i))
  · intro a' ha'
    have hcover : ∀ z : Z, ∃ i, z ∈ B i := by
      intro z
      obtain ⟨V, ⟨i, rfl⟩, hi, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB
        (show z ∈ (⊤ : Z.Opens) from trivial)
      exact ⟨i, hi⟩
    apply AbelianModuli.HilbertConstruction.Module.MapCoverEquality.moduleMap_eq_of_pullback_cover B hcover
    intro i
    rw [ha i]
    have h := congrArg (fun b => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (B i).ι).hom ≫ b) (ha' i)
    simpa only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Iso.hom_inv_id_assoc] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenSectionGluing.Construction
