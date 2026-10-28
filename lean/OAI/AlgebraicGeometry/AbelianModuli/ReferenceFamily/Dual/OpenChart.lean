import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualAffineCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts

/-! # Open Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenChart

noncomputable section

/-! Actual open subfamilies and their maps into the original affine
cover charts of a varying dual-number family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [CommRing k] (X : Over (Spec (.of (DualNumber k))))

def dualFamilyOpenObject (V : X.left.Opens) : Over (Spec (.of (DualNumber k))) :=
  Over.mk (V.ι ≫ X.hom)

def dualFamilyOpenInclusion (V : X.left.Opens) : dualFamilyOpenObject k X V ⟶ X :=
  Over.homMk V.ι

theorem dualFamilyOpenObject_affine (V : X.left.Opens) (hV : IsAffineOpen V) :
    IsAffine (dualFamilyOpenObject k X V).left := hV

theorem dualFamilyOpenObject_smooth [Smooth X.hom] (V : X.left.Opens) :
    Smooth (dualFamilyOpenObject k X V).hom :=
  inferInstanceAs (Smooth (V.ι ≫ X.hom))

theorem dualFamilyOpenInclusion_open (V : X.left.Opens) :
    IsOpenImmersion (dualFamilyOpenInclusion k X V).left :=
  inferInstanceAs (IsOpenImmersion V.ι)

def dualFamilyOpenMap {V W : X.left.Opens} (h : V ≤ W) :
    dualFamilyOpenObject k X V ⟶ dualFamilyOpenObject k X W :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ (W.ι ≫ X.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem dualFamilyOpenMap_inclusion {V W : X.left.Opens} (h : V ≤ W) :
    dualFamilyOpenMap k X h ≫ dualFamilyOpenInclusion k X W = dualFamilyOpenInclusion k X V := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left h

variable (U : X.left.AffineOpenCover) (i : U.I₀) (V : X.left.Opens)

theorem dualFamilyAffineChartInclusion_open :
    IsOpenImmersion (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i).left :=
  inferInstanceAs (IsOpenImmersion (U.f i))

theorem dualFamilyOpen_chart_range (hV : V ≤ (U.f i).opensRange) :
    Set.range (dualFamilyOpenInclusion k X V).left ⊆
      Set.range (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i).left := by
  change Set.range V.ι ⊆ Set.range (U.f i)
  rw [Scheme.Opens.range_ι]
  exact hV

def dualFamilyOpenLiftToChart (hV : V ≤ (U.f i).opensRange) :
    dualFamilyOpenObject k X V ⟶ ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChart k X U i := by
  have := dualFamilyAffineChartInclusion_open k X U i
  exact DualOpen.Lifts.overOpenLift (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i) (dualFamilyOpenInclusion k X V)
    (dualFamilyOpen_chart_range k X U i V hV)

theorem dualFamilyOpenLiftToChart_fac (hV : V ≤ (U.f i).opensRange) :
    dualFamilyOpenLiftToChart k X U i V hV ≫ ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i =
      dualFamilyOpenInclusion k X V := by
  have := dualFamilyAffineChartInclusion_open k X U i
  exact DualOpen.Lifts.overOpenLift_fac (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i) (dualFamilyOpenInclusion k X V)
    (dualFamilyOpen_chart_range k X U i V hV)

theorem dualFamilyOpenLiftToChart_open (hV : V ≤ (U.f i).opensRange) :
    IsOpenImmersion (dualFamilyOpenLiftToChart k X U i V hV).left := by
  have := dualFamilyAffineChartInclusion_open k X U i
  have hc : IsOpenImmersion
      ((dualFamilyOpenLiftToChart k X U i V hV ≫ ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i).left) :=
    (congrArg (fun f : dualFamilyOpenObject k X V ⟶ X => IsOpenImmersion f.left)
      (dualFamilyOpenLiftToChart_fac k X U i V hV)).mpr (dualFamilyOpenInclusion_open k X V)
  change IsOpenImmersion ((dualFamilyOpenLiftToChart k X U i V hV).left ≫
    (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i).left) at hc
  exact IsOpenImmersion.of_comp (dualFamilyOpenLiftToChart k X U i V hV).left
    (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i).left

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenChart
