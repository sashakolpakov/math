import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.StructureSheafMap

/-! # Scheme Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.SchemeMorphism

noncomputable section

/-! The constructed Veronese map of sheafed spaces has the expected
local ring maps on stalks, hence is an actual scheme morphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization _root_.TopologicalSpace
open ProjectiveSpectrum.StructureSheaf
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]

def veroneseStalkFraction (p : ProjectiveSpectrum g)
    (c : NumDenSameDeg (Grading.veroneseGrading g N)
      (ProjectiveComap.veroneseProjectiveComap g N p).asHomogeneousIdeal.toIdeal.primeCompl) :
    NumDenSameDeg g p.asHomogeneousIdeal.toIdeal.primeCompl where
  deg := N * c.deg
  num := ⟨c.num.val.val, c.num.property⟩
  den := ⟨c.den.val.val, c.den.property⟩
  den_mem := c.den_mem

theorem veronese_germ_map_sectionInBasicOpen {p : ProjectiveSpectrum g}
    (c : NumDenSameDeg (Grading.veroneseGrading g N)
      (ProjectiveComap.veroneseProjectiveComap g N p).asHomogeneousIdeal.toIdeal.primeCompl) :
    (Proj.toSheafedSpace g).presheaf.germ
      ((Opens.map (StructureSheafMap.veroneseSheafedSpaceMap g N).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((StructureSheafMap.veroneseSheafedSpaceMap g N).hom.c.app _
        (sectionInBasicOpen (Grading.veroneseGrading g N) (ProjectiveComap.veroneseProjectiveComap g N p) c)) =
      (Proj.toSheafedSpace g).presheaf.germ
        (ProjectiveSpectrum.basicOpen g c.den.val.val) p c.den_mem
        (sectionInBasicOpen g p (veroneseStalkFraction g N p c)) := rfl

theorem veroneseHomogeneousStalkMap_val (p : ProjectiveSpectrum g)
    (x : HomogeneousLocalization.AtPrime (Grading.veroneseGrading g N)
      (ProjectiveComap.veroneseProjectiveComap g N p).asHomogeneousIdeal.toIdeal) :
    (StructureSheafMap.veroneseHomogeneousStalkMap g N p x).val =
      Localization.localRingHom _ _ (Subalgebra.veroneseSubalgebra g N).val.toRingHom rfl x.val :=
  HomogeneousLocalRingMap.regradedHomogeneousLocalRingMap_val _ _ _ _ _ _ _ _ x

theorem veronese_stalkMap_comparison (p : ProjectiveSpectrum g) :
    (Proj.stalkIso (Grading.veroneseGrading g N) (ProjectiveComap.veroneseProjectiveComap g N p)).hom ≫
      CommRingCat.ofHom (StructureSheafMap.veroneseHomogeneousStalkMap g N p) ≫ (Proj.stalkIso g p).inv =
        (StructureSheafMap.veroneseSheafedSpaceMap g N).hom.stalkMap p := by
  erw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, Proj.stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [veroneseHomogeneousStalkMap_val, HomogeneousLocalization.val_mk,
    RingHom.comp_apply, Localization.localRingHom_mk]
  erw [Proj.stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [veronese_germ_map_sectionInBasicOpen]
  erw [Proj.stalkIso'_germ]
  rfl

def veroneseSchemeMorphism : Proj g ⟶ Proj (Grading.veroneseGrading g N) where
  __ := (StructureSheafMap.veroneseSheafedSpaceMap g N).hom
  prop p := .mk fun x hx => by
    erw [← veronese_stalkMap_comparison] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (Proj.stalkIso g p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := (isUnit_map_iff (StructureSheafMap.veroneseHomogeneousStalkMap g N p) _).mp hx
    have : IsLocalHom (Proj.stalkIso (Grading.veroneseGrading g N) (ProjectiveComap.veroneseProjectiveComap g N p)).hom.hom :=
      isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

theorem veroneseSchemeMorphism_preimage_basicOpen (f : Subalgebra.veroneseSubalgebra g N) :
    veroneseSchemeMorphism g N ⁻¹ᵁ Proj.basicOpen (Grading.veroneseGrading g N) f =
      Proj.basicOpen g f.val := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.SchemeMorphism
