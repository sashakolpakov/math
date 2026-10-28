import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps

/-! # Coefficient Normal Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientNormalPurity

noncomputable section

/-! The normal residue of a coefficient vector is the original
contravariant map on resolution cohomology followed by oriented purity. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation
variable (R : Type u) [CommRing R] {c : ℕ} (s : Fin c → R)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (P : ProjectiveResolution (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s)))
  {M : ModuleCat.{u} R} (Q : ProjectiveResolution M)
  (β : ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s) ⟶ M)

def map : DualComplexHomology.complex R Q.complex ⟶
    (single (ModuleCat R) (.up ℕ) c).obj (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s)) :=
  DualComplexHomology.map R
      (ProjectiveResolution.lift β (KoszulPartial.Resolution.normalResolution R s hreg) Q) ≫
    ResidueHomology.map R s

theorem homology : homologyMap (map R s hreg Q β) c ≫
    (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of R (R ⧸ OrientedTopCohomology.ideal R s))).hom =
      Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R) P Q β c ≫
        (ResolutionOrientation.purityIso R (OrientedTopCohomology.ideal R s) s rfl hreg P).hom := by
  have hp := NormalPurity.homology R s hreg P
  rw [NormalPurity.map, homologyMap_comp, Category.assoc,
    ResidueHomology.homology] at hp
  change Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R)
    (KoszulPartial.Resolution.normalResolution R s hreg) P (𝟙 _) c ≫
      (OrientedTopCohomology.iso R s).hom = _ at hp
  rw [map, homologyMap_comp, Category.assoc, ResidueHomology.homology]
  change Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R)
    (KoszulPartial.Resolution.normalResolution R s hreg) Q β c ≫
      (OrientedTopCohomology.iso R s).hom = _
  have h := Resolution.CohomologyMaps.map_comp (ExactModuleDualFunctor.functor R)
    (KoszulPartial.Resolution.normalResolution R s hreg) P Q (𝟙 _) β c
  rw [Category.id_comp] at h
  rw [h, Category.assoc, hp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientNormalPurity
