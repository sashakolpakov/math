import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Open Cech Short Complex -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex.Construction

noncomputable section

/-! The first three terms of the actual open-cover Cech complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    (F : TopCat.Sheaf (ModuleCat.{v} R) X) {ι : Type v} (U : ι → Opens X)

abbrev openModuleCechC2 := ∀ i j k, F.obj.obj (op ((U i ⊓ U j) ⊓ U k))

def openCechRestrict1Linear (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    OpenCechDegreeZero.Construction.openModuleCechC1 F U →ₗ[R] F.obj.obj (op W) where
  toFun z := OpenCechCocycles.Construction.openCechRestrict1 F U z i j W hi hj
  map_add' z w := (F.obj.map (homOfLE (le_inf hi hj)).op).hom.map_add (z i j) (w i j)
  map_smul' r z := (F.obj.map (homOfLE (le_inf hi hj)).op).hom.map_smul r (z i j)

def openModuleCechD1 : OpenCechDegreeZero.Construction.openModuleCechC1 F U →ₗ[R] openModuleCechC2 F U :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    openCechRestrict1Linear F U i j ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
    openCechRestrict1Linear F U j k ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_right) inf_le_right -
    openCechRestrict1Linear F U i k ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_left) inf_le_right

theorem openModuleCechD1_eq_zero_iff (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) :
    openModuleCechD1 F U z = 0 ↔ OpenCechCocycles.Construction.IsOpenCechCocycle F U z := by
  constructor
  · intro hz i j k W hi hj hk
    have hz' := congrFun (congrFun (congrFun hz i) j) k
    change OpenCechCocycles.Construction.openCechRestrict1 F U z i j ((U i ⊓ U j) ⊓ U k)
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
      OpenCechCocycles.Construction.openCechRestrict1 F U z j k ((U i ⊓ U j) ⊓ U k)
        (inf_le_left.trans inf_le_right) inf_le_right -
      OpenCechCocycles.Construction.openCechRestrict1 F U z i k ((U i ⊓ U j) ⊓ U k)
        (inf_le_left.trans inf_le_left) inf_le_right = 0 at hz'
    have h := congrArg (F.obj.map (homOfLE (le_inf (le_inf hi hj) hk)).op)
      (sub_eq_zero.mp hz')
    rw [map_add, OpenCechCocycles.Construction.openCechRestrict1_comp, OpenCechCocycles.Construction.openCechRestrict1_comp, OpenCechCocycles.Construction.openCechRestrict1_comp] at h
    exact h
  · intro hz
    funext i j k
    exact sub_eq_zero.mpr (hz i j k ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)

theorem openModuleCechD1_comp_D0 : (openModuleCechD1 F U).comp (OpenCechDegreeZero.Construction.openModuleCechD0 F U) = 0 := by
  apply LinearMap.ext
  intro x
  exact (openModuleCechD1_eq_zero_iff F U _).mpr (OpenCechCocycles.Construction.openCechD0_isCocycle F U x)

abbrev openModuleCechShortComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (OpenCechDegreeZero.Construction.openModuleCechD0 F U) (openModuleCechD1 F U)
    (openModuleCechD1_comp_D0 F U)

theorem openModuleCechD1_kernel : LinearMap.ker (openModuleCechD1 F U) = OpenCechCohomology.Construction.openCechCocycles F U := by
  ext z
  exact openModuleCechD1_eq_zero_iff F U z

def openModuleCechCyclesEquiv : LinearMap.ker (openModuleCechD1 F U) ≃ₗ[R] OpenCechCohomology.Construction.openCechCocycles F U :=
  LinearEquiv.ofEq _ _ (openModuleCechD1_kernel F U)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex.Construction
