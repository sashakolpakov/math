import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeVectorSpaceContraction
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Open Cech Degree Zero -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech

noncomputable section

/-! Exactness in degree zero for module-valued Cech cochains on an open cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v w

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    (F : TopCat.Sheaf (ModuleCat.{v} R) X) {ι : Type w} (U : ι → Opens X)

abbrev openModuleCechC0 := ∀ i, F.obj.obj (op (U i))
abbrev openModuleCechC1 := ∀ i j, F.obj.obj (op (U i ⊓ U j))

def openModuleCechUnit : F.obj.obj (op ⊤) →ₗ[R] openModuleCechC0 F U :=
  LinearMap.pi fun i ↦ (F.obj.map (homOfLE le_top : U i ⟶ ⊤).op).hom

def openModuleCechD0 : openModuleCechC0 F U →ₗ[R] openModuleCechC1 F U :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (F.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op).hom.comp (LinearMap.proj j) -
      (F.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op).hom.comp (LinearMap.proj i)

theorem openModuleCechD0_eq_zero_iff (x : openModuleCechC0 F U) :
    openModuleCechD0 F U x = 0 ↔ TopCat.Presheaf.IsCompatible F.obj U x := by
  constructor
  · intro hx i j
    exact (sub_eq_zero.mp (congrFun (congrFun hx i) j)).symm
  · intro hx
    funext i j
    exact sub_eq_zero.mpr (hx i j).symm

theorem openModuleCech_sections_glue (hU : iSup U = ⊤)
    (x : openModuleCechC0 F U) (hx : openModuleCechD0 F U x = 0) :
    ∃! s : F.obj.obj (op ⊤), openModuleCechUnit F U s = x := by
  obtain ⟨s, hs, huniq⟩ := F.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    hU.ge x ((openModuleCechD0_eq_zero_iff F U x).mp hx)
  refine ⟨s, funext hs, ?_⟩
  intro t ht
  apply huniq t
  intro i
  exact congrFun ht i

theorem openModuleCech_exact_degreeZero (hU : iSup U = ⊤) :
    Function.Exact (openModuleCechUnit F U) (openModuleCechD0 F U) := by
  intro x
  constructor
  · intro hx
    obtain ⟨s, hs, _⟩ := openModuleCech_sections_glue F U hU x hx
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    funext i j
    change F.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op
      (F.obj.map (homOfLE le_top : U j ⟶ ⊤).op s) -
      F.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op
        (F.obj.map (homOfLE le_top : U i ⟶ ⊤).op s) = 0
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.obj.map_comp,
      ← F.obj.map_comp]
    exact sub_self _

theorem openModuleCechUnit_injective (hU : iSup U = ⊤) :
    Function.Injective (openModuleCechUnit F U) := by
  intro s t hst
  apply F.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) hU.ge
  intro i
  exact congrFun hst i

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech
