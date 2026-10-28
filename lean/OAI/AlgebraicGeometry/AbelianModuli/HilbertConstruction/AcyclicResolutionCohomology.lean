import Mathlib.CategoryTheory.Sites.Limits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.BoundaryCokernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomologySpecifiedCycles
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Acyclic Resolution Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionCohomology.IntrinsicCech

noncomputable section

/-! Global sections of an acyclic sheaf resolution compute actual sheaf cohomology in every degree. The comparison is constructed from cycle kernels and the connecting homomorphisms of short exact sheaf sequences. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] comp_preservesFiniteLimits
variable {X : TopCat.{u}}

def sheafTopEvaluation (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

instance sheafTopEvaluation_additive : (sheafTopEvaluation X).Additive where
  map_add := by intros; rfl

instance sheafTopEvaluation_preservesFiniteLimits : PreservesFiniteLimits (sheafTopEvaluation X) := by
  have : PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  have : PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) := inferInstance
  exact comp_preservesFiniteLimits _ _

def sheafTopSectionsComplex (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((sheafTopEvaluation X).mapHomologicalComplex (.up ℕ)).obj K

def sheafTopSectionsHomologyCokernelIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) (n : ℕ) :
    (sheafTopSectionsComplex K).homology (n + 1) ≅
      cokernel ((AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).toCycles.hom.app (op ⊤)) := by
  let S := AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n
  let E := sheafTopEvaluation X
  have : E.Additive := inferInstanceAs ((sheafTopEvaluation X).Additive)
  let C := sheafTopSectionsComplex K
  have wi : E.map S.iCycles ≫ (S.map E).g = 0 := by
    change E.map S.iCycles ≫ E.map S.g = 0
    rw [← E.map_comp, S.iCycles_g, E.map_zero]
  have hi : IsLimit (KernelFork.ofι (E.map S.iCycles) wi) :=
    KernelFork.mapIsLimit _ S.cyclesIsKernel E
  have ha : E.map S.toCycles ≫ E.map S.iCycles = (S.map E).f := by
    rw [← E.map_comp, S.toCycles_i]
    rfl
  exact C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    HomologySpecifiedCycles.homologySpecifiedCyclesIso (S.map E) (E.map S.iCycles) wi hi (E.map S.toCycles) ha

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ⟶ K.X 0)
    (w : e ≫ K.d 0 1 = 0) [he : Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (hK : ∀ p q, Subsingleton (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (q + 1) :
      _ ⥤ AddCommGrpCat.{u}).obj (K.X p))))

include he

def acyclicResolutionPositiveCohomologyIso (n : ℕ) :
    (sheafTopSectionsComplex K).homology (n + 1) ≅
      AddCommGrpCat.of (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1) :
        _ ⥤ AddCommGrpCat.{u}).obj F)) := by
  refine sheafTopSectionsHomologyCokernelIso K n ≪≫ ?_
  cases n with
  | zero =>
      exact HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso
        (AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact K e w haug hpos) (hK 0 0)
  | succ n =>
      exact HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso
          (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hpos n) (hK (n + 1) 0) ≪≫
        (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift K e w haug hpos hK n 0).toAddCommGrpIso

def acyclicResolutionCohomologyIso (n : ℕ) :
    (sheafTopSectionsComplex K).homology n ≅
      AddCommGrpCat.of (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n :
        _ ⥤ AddCommGrpCat.{u}).obj F)) := by
  cases n with
  | succ n => exact acyclicResolutionPositiveCohomologyIso K e w haug hpos hK n
  | zero =>
      let E := sheafTopEvaluation X
      have : E.Additive := inferInstanceAs ((sheafTopEvaluation X).Additive)
      have : PreservesFiniteLimits E := inferInstanceAs (PreservesFiniteLimits (sheafTopEvaluation X))
      let C := sheafTopSectionsComplex K
      have wc : E.map e ≫ C.d 0 1 = 0 := by
        change E.map e ≫ E.map (K.d 0 1) = 0
        rw [← E.map_comp, w, E.map_zero]
      have hex : (ShortComplex.mk (E.map e) (C.d 0 1) wc).Exact :=
        haug.map_of_mono_of_preservesKernel E inferInstance inferInstance
      let f := C.liftCycles (E.map e) 1 (by simp) wc
      have : IsIso f := (CochainComplex.isIso_liftCycles_iff C (E.map e) wc).mpr
        ⟨hex, inferInstance⟩
      exact C.isoHomologyπ₀.symm ≪≫ (asIso f).symm ≪≫
        (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).symm.toAddCommGrpIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionCohomology.IntrinsicCech
