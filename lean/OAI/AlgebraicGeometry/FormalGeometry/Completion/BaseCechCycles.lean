import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CompatibleCycles
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FunctionsComparison

/-! # Base Cech Cycles -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechCycles.Construction

noncomputable section

/-! The actual base-ring map into native Cech zero-cycles and its infinitesimal coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual global base-ring map with its literal R-linear structure. -/
def baseGlobalSectionsLinearMap : R →ₗ[R] (RelativeStructureSections.Construction.relativeStructureSections f).obj (op ⊤) where
  toFun := Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤
  map_add' := map_add _
  map_smul' r s := (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤).map_mul r s

theorem baseGlobalSectionsLinearMap_bijective [IsIso f.appTop] :
    Function.Bijective (baseGlobalSectionsLinearMap f) := by
  have he : Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤ =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom := by
    simp [Affine.InfinitesimalSections.Construction.baseOpenSectionsMap, Scheme.Hom.appTop, Scheme.Hom.appLE]
  change Function.Bijective (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤)
  rw [he]
  exact ConcreteCategory.bijective_of_isIso _

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hcover : iSup U = ⊤)

/-- A base coefficient gives its actual constant Cech zero-cycle. -/
def baseCechCycleMap : R →ₗ[R] ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.ker :=
  (RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv f U hcover).toLinearMap.comp
    (baseGlobalSectionsLinearMap f)

theorem baseCechCycleMap_bijective [IsIso f.appTop] :
    Function.Bijective (baseCechCycleMap f U hcover) :=
  (RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv f U hcover).bijective.comp
    (baseGlobalSectionsLinearMap_bijective f)

theorem baseCechCycleMap_coordinate (r : R) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    Infinitesimal.SectionCoordinates.Construction.relativeCechProjection f U 0 a (baseCechCycleMap f U hcover r).val =
      Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f (∏ᶜ fun k : Fin 1 => U (a.val k)) r := by
  have hc := (RelativeCechTerms.Construction.relativeStructureCechTermIso_coordinate f U 0
    (baseCechCycleMap f U hcover r).val a).trans
      (RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv_coordinate f U hcover
        (baseGlobalSectionsLinearMap f r) a)
  exact hc.trans (RingHom.congr_fun (Infinitesimal.ChartRestriction.Construction.baseOpenSectionsMap_restrict f le_top) r)

variable (I : Ideal R) [X.IsSeparated] [Finite ι] (hU : ∀ i, IsAffineOpen (U i))

/-- The reduced constant zero-cycle is the actual infinitesimal structure-map section. -/
theorem infinitesimalSectionsZeroCyclesEquiv_base_mk (n : ℕ) (r : R) :
    (Infinitesimal.CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n
      (FunctionsComparison.Construction.infinitesimalBaseSectionsMap I f n (Ideal.Quotient.mk (I ^ (n + 1)) r))).val =
        Submodule.Quotient.mk ((baseCechCycleMap f U hcover r).val) := by
  apply Infinitesimal.ZeroCycleTransitions.Construction.relativeCechReducedCoordinates_ext (I ^ (n + 1)) f U 0
  intro a
  let V := ∏ᶜ fun k : Fin 1 => U (a.val k)
  have hV : IsAffineOpen V := SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU 0 a.val
  apply (Infinitesimal.ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n V hV).injective
  have hc := Infinitesimal.ChartZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv_chart I f U hU hcover n
    (FunctionsComparison.Construction.infinitesimalBaseSectionsMap I f n (Ideal.Quotient.mk (I ^ (n + 1)) r)) a
  refine hc.trans ?_
  rw [LinearMap.reduceModIdeal_apply,
    baseCechCycleMap_coordinate, Infinitesimal.ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv_mk,
    RelativeStructureSections.Construction.relativeStructureSectionsPullback_apply]
  have hs : (Scheme.ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
      (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appTop ≫
        (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood I f n).presheaf.map
          (homOfLE (show pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ V ≤ ⊤ from le_top)).op =
      Affine.InfinitesimalSections.Construction.infinitesimalOpenBaseSectionsMap I f n V := by
    rfl
  have hp := ConcreteCategory.congr_hom
    (Affine.InfinitesimalSections.Construction.affineInfinitesimalSections_isPushout I f n V hV).w r
  exact (ConcreteCategory.congr_hom hs (Ideal.Quotient.mk (I ^ (n + 1)) r)).trans hp.symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechCycles.Construction
