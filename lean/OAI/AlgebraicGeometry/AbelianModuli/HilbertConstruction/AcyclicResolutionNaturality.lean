import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedComplexZeroComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.ResolutionNaturality

/-! # Acyclic Resolution Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionNaturality.IntrinsicCech

noncomputable section

/-! Naturality in every degree of the acyclic-resolution cohomology comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private abbrev cohomologyMap {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) :=
  (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).map f

private def zeroSectionsIso {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X).obj F ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0 : _ ⥤ AddCommGrpCat.{u}).obj F :=
  (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).symm.toAddCommGrpIso

private theorem degree_zero_naturality {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) :
    (AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X).map f ≫ (zeroSectionsIso G).hom =
      (zeroSectionsIso F).hom ≫ cohomologyMap f 0 := by
  ext x
  exact (CategoryTheory.Sheaf.H.equiv₀_symm_naturality isTerminalTop f x).symm

private def zeroComparisonIso {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ⟶ K.X 0)
    (w : e ≫ K.d 0 1 = 0) [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact) :
    (AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex K).homology 0 ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0 : _ ⥤ AddCommGrpCat.{u}).obj F := by
  let E : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} := AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X
  have : E.Additive := inferInstanceAs ((AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X).Additive)
  have : PreservesFiniteLimits E := inferInstanceAs (PreservesFiniteLimits (AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X))
  let C := AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex K
  have wc : E.map e ≫ C.d 0 1 = 0 := by
    change E.map e ≫ E.map (K.d 0 1) = 0
    rw [← E.map_comp, w, E.map_zero]
  have hex : (ShortComplex.mk (E.map e) (C.d 0 1) wc).Exact :=
    haug.map_of_mono_of_preservesKernel E inferInstance inferInstance
  exact AugmentedComplexZeroComparison.IntrinsicCech.AugmentedZero.comparisonWithIso C (E.map e) wc hex (zeroSectionsIso F)

variable {X : TopCat.{u}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (eK : F ⟶ K.X 0) (wK : eK ≫ K.d 0 1 = 0) [Mono eK]
    (eL : G ⟶ L.X 0) (wL : eL ≫ L.d 0 1 = 0) [Mono eL]
    (haugK : (ShortComplex.mk eK (K.d 0 1) wK).Exact)
    (haugL : (ShortComplex.mk eL (L.d 0 1) wL).Exact)

private theorem acyclicResolutionCohomologyIso_zero_naturality
    (f : F ⟶ G) (ψ : K ⟶ L) (hψ : f ≫ eL = eK ≫ ψ.f 0) :
    HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) 0 ≫ (zeroComparisonIso L eL wL haugL).hom =
      (zeroComparisonIso K eK wK haugK).hom ≫ cohomologyMap f 0 := by
  let E : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} := AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X
  have : E.Additive := inferInstanceAs ((AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X).Additive)
  have : PreservesFiniteLimits E := inferInstanceAs (PreservesFiniteLimits (AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X))
  let C := AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex K
  let D := AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex L
  have wc : E.map eK ≫ C.d 0 1 = 0 := by
    change E.map eK ≫ E.map (K.d 0 1) = 0
    rw [← E.map_comp, wK, E.map_zero]
  have wd : E.map eL ≫ D.d 0 1 = 0 := by
    change E.map eL ≫ E.map (L.d 0 1) = 0
    rw [← E.map_comp, wL, E.map_zero]
  have hc : (ShortComplex.mk (E.map eK) (C.d 0 1) wc).Exact :=
    haugK.map_of_mono_of_preservesKernel E inferInstance inferInstance
  have hd : (ShortComplex.mk (E.map eL) (D.d 0 1) wd).Exact :=
    haugL.map_of_mono_of_preservesKernel E inferInstance inferInstance
  have hmap : E.map f ≫ E.map eL = E.map eK ≫ (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ).f 0 := by
    change E.map f ≫ E.map eL = E.map eK ≫ E.map (ψ.f 0)
    rw [← E.map_comp, ← E.map_comp, hψ]
  let bF := zeroSectionsIso F
  let bG := zeroSectionsIso G
  have hb := degree_zero_naturality f
  have result := AugmentedComplexZeroComparison.IntrinsicCech.AugmentedZero.naturalityWithIso (K := C) (L := D)
    (E.map eK) wc (E.map eL) wd hc hd (E.map f) (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) hmap
    bF bG (cohomologyMap f 0) hb
  exact result

variable
    (hposK : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (hposL : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L n).Exact)
    (hK : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (L.X p) (q + 1)))
    (f : F ⟶ G) (ψ : K ⟶ L) (hψ : f ≫ eL = eK ≫ ψ.f 0)

include hψ in
theorem acyclicResolutionCohomologyIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) n ≫
        (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionCohomologyIso L eL wL haugL hposL hL n).hom =
      (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionCohomologyIso K eK wK haugK hposK hK n).hom ≫
        cohomologyMap f n := by
  cases n with
  | zero =>
      have result := acyclicResolutionCohomologyIso_zero_naturality eK wK eL wL haugK haugL f ψ hψ
      exact result
  | succ n =>
      have result := Positive.ResolutionNaturality.IntrinsicCech.acyclicResolutionPositiveCohomologyIso_naturality eK wK eL wL haugK haugL
        hposK hposL hK hL f ψ hψ n
      exact result

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionNaturality.IntrinsicCech
