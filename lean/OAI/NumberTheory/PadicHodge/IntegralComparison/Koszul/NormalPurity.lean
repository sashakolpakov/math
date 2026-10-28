import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResidueHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution

/-! # Normal Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalPurity

noncomputable section

/-! The canonical comparison to the original normal Koszul resolution,
followed by its cochain residue, is the previously defined oriented purity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] {c : ℕ} (s : Fin c → R)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation

theorem augmentation :
    (ResolutionOrientation.resolutionAtIdeal R (OrientedTopCohomology.ideal R s) s rfl hreg).π =
      (KoszulPartial.Resolution.normalResolution R s hreg).π := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
      rw [ResolutionOrientation.resolutionAtIdeal_π_zero, Exterior.KoszulResolution.resolution_π_f_zero]
      rfl
  | succ i =>
      exact (isZero_single_obj_X (.down ℕ) 0 (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s))
        (i+1) (by omega)).eq_of_tgt _ _

variable (P : ProjectiveResolution (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s)))

theorem comparison_eq :
    (ResolutionOrientation.comparison R P (KoszulPartial.Resolution.normalResolution R s hreg) c).hom =
      (ResolutionOrientation.comparison R P (ResolutionOrientation.resolutionAtIdeal R (OrientedTopCohomology.ideal R s) s rfl hreg) c).hom := by
  have h := ResolutionOrientation.comparison_naturality R P
    (ResolutionOrientation.resolutionAtIdeal R (OrientedTopCohomology.ideal R s) s rfl hreg)
    (KoszulPartial.Resolution.normalResolution R s hreg)
    (𝟙 _) (by simpa only [Category.id_comp] using augmentation R s hreg) c
  have hid : DualComplexHomology.map R
      (𝟙 (OrientedTopCohomology.koszul R s)) = 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro x
    rfl
  erw [hid, homologyMap_id, Category.comp_id] at h
  exact h.symm

def map : DualComplexHomology.complex R P.complex ⟶
    (single (ModuleCat R) (.up ℕ) c).obj (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s)) :=
  DualComplexHomology.map R
      (ProjectiveResolution.lift (𝟙 _) (KoszulPartial.Resolution.normalResolution R s hreg) P) ≫
    ResidueHomology.map R s

theorem homology : homologyMap (map R s hreg P) c ≫
    (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s))).hom =
      (ResolutionOrientation.purityIso R (OrientedTopCohomology.ideal R s) s rfl hreg P).hom := by
  rw [map, homologyMap_comp, Category.assoc, ResidueHomology.homology]
  change (ResolutionOrientation.comparison R P (KoszulPartial.Resolution.normalResolution R s hreg) c).hom ≫
    (OrientedTopCohomology.iso R s).hom = _
  rw [comparison_eq]
  change _ = (ResolutionOrientation.comparison R P (ResolutionOrientation.resolutionAtIdeal R (OrientedTopCohomology.ideal R s) s rfl hreg) c).hom ≫
    ((OrientedTopCohomology.iso R s).hom ≫
      (Submodule.quotEquivOfEq (OrientedTopCohomology.ideal R s) (OrientedTopCohomology.ideal R s) rfl).toModuleIso.hom)
  have he : (Submodule.quotEquivOfEq (OrientedTopCohomology.ideal R s) (OrientedTopCohomology.ideal R s) rfl).toModuleIso.hom = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (OrientedTopCohomology.ideal R s) x
    rfl
  erw [he, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalPurity
