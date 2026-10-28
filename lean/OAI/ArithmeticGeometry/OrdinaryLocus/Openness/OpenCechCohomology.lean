import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCocycles
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Open Cech Cohomology -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCohomology.Construction

noncomputable section

/-! First Cech cohomology of an open family with coefficients in a module sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v w

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    (F : TopCat.Sheaf (ModuleCat.{v} R) X) {ι : Type w} (U : ι → Opens X)

def openCechCocycles : Submodule R (OpenCechDegreeZero.Construction.openModuleCechC1 F U) where
  carrier := OpenCechCocycles.Construction.IsOpenCechCocycle F U
  zero_mem' := by
    intro i j k W hi hj hk
    simp [OpenCechCocycles.Construction.openCechRestrict1]
  add_mem' := by
    intro a b ha hb i j k W hi hj hk
    simp only [OpenCechCocycles.Construction.openCechRestrict1, Pi.add_apply, map_add]
    change (OpenCechCocycles.Construction.openCechRestrict1 F U a i j W hi hj + OpenCechCocycles.Construction.openCechRestrict1 F U b i j W hi hj) +
      (OpenCechCocycles.Construction.openCechRestrict1 F U a j k W hj hk + OpenCechCocycles.Construction.openCechRestrict1 F U b j k W hj hk) = _
    rw [add_add_add_comm, ha i j k W hi hj hk, hb i j k W hi hj hk]
    rfl
  smul_mem' := by
    intro r a ha i j k W hi hj hk
    simp only [OpenCechCocycles.Construction.openCechRestrict1, Pi.smul_apply, map_smul]
    exact (smul_add r _ _).symm.trans (congrArg (fun x ↦ r • x) (ha i j k W hi hj hk))

def openCechBoundaryMap : OpenCechDegreeZero.Construction.openModuleCechC0 F U →ₗ[R] openCechCocycles F U :=
  (OpenCechDegreeZero.Construction.openModuleCechD0 F U).codRestrict (openCechCocycles F U) (OpenCechCocycles.Construction.openCechD0_isCocycle F U)

abbrev OpenCechH1 := openCechCocycles F U ⧸ LinearMap.range (openCechBoundaryMap F U)

def openCechClass (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (hz : OpenCechCocycles.Construction.IsOpenCechCocycle F U z) : OpenCechH1 F U :=
  Submodule.Quotient.mk ⟨z, hz⟩

theorem openCechClass_eq_zero_iff (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (hz : OpenCechCocycles.Construction.IsOpenCechCocycle F U z) :
    openCechClass F U z hz = 0 ↔ ∃ x, OpenCechDegreeZero.Construction.openModuleCechD0 F U x = z := by
  rw [openCechClass, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

theorem openCechClass_surjective (q : OpenCechH1 F U) :
    ∃ (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (hz : OpenCechCocycles.Construction.IsOpenCechCocycle F U z), openCechClass F U z hz = q := by
  obtain ⟨z, rfl⟩ := (LinearMap.range (openCechBoundaryMap F U)).mkQ_surjective q
  exact ⟨z.val, z.property, rfl⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCohomology.Construction
