import OAI.AlgebraicGeometry.Comparison.Betti.PointModulePresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Point Module Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PointModuleFunctor.Local

noncomputable section

section

/-! The actual point-supported module presheaf satisfies the sheaf
condition: compatible local point values glue uniquely. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : TopCat.Presheaf RingCat.{0} X) (x : X)

theorem pointModulePresheaf_isSheaf (N : ModuleCat.{0} (R.stalk x)) :
    TopCat.Presheaf.IsSheaf (C := AddCommGrpCat) (X := X) (PointModulePresheaf.Local.pointModulePresheaf R x N).presheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (PointModulePresheaf.Local.pointModulePresheaf R x N).presheaf).2
  intro ι U a ha
  let s : ∀ i, (x ∈ U i) → N := fun i hi => a i ⟨hi⟩
  have hs : ∀ i j (hi : x ∈ U i) (hj : x ∈ U j), s i hi = s j hj := by
    intro i j hi hj
    exact congrArg (fun b : PLift (x ∈ U i ⊓ U j) → N => b ⟨⟨hi, hj⟩⟩) (ha i j)
  let idx (h : x ∈ iSup U) : ι := (Opens.mem_iSup.mp h).choose
  have hidx (h : x ∈ iSup U) : x ∈ U (idx h) := (Opens.mem_iSup.mp h).choose_spec
  let b : PLift (x ∈ iSup U) → N := fun h => s (idx h.down) (hidx h.down)
  refine ⟨b, ?_, ?_⟩
  · intro i
    funext hi
    exact hs (idx ((le_iSup U i) hi.down)) i (hidx ((le_iSup U i) hi.down)) hi.down
  · intro c hc
    change PLift (x ∈ iSup U) → N at c
    funext h
    have hh := congrArg (fun v : PLift (x ∈ U (idx h.down)) → N => v ⟨hidx h.down⟩) (hc (idx h.down))
    exact hh

def pointModuleSheaf (S : TopCat.Sheaf RingCat.{0} X) (x : X)
    (N : ModuleCat.{0} (TopCat.Presheaf.stalk (C := RingCat) (X := X) S.obj x)) :
    SheafOfModules.{0} S :=
  ⟨PointModulePresheaf.Local.pointModulePresheaf S.obj x N, pointModulePresheaf_isSheaf S.obj x N⟩

end

/-! The actual point-supported module constructions are functorial
in the module over the local ring. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {X : TopCat.{0}}

def pointModulePresheafFunctor (R : TopCat.Presheaf RingCat.{0} X) (x : X) :
    ModuleCat.{0} (R.stalk x) ⥤ PresheafOfModules.{0} R where
  obj := PointModulePresheaf.Local.pointModulePresheaf R x
  map := PointModulePresheaf.Local.pointModulePresheafMap R x
  map_id N := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext hx
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext hx
    rfl

def pointModuleSheafFunctor (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}) (x : X) :
    ModuleCat.{0} (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x) ⥤ SheafOfModules.{0} R where
  obj := pointModuleSheaf R x
  map f := ⟨PointModulePresheaf.Local.pointModulePresheafMap R.obj x f⟩
  map_id N := SheafOfModules.Hom.ext ((pointModulePresheafFunctor R.obj x).map_id N)
  map_comp f g := SheafOfModules.Hom.ext ((pointModulePresheafFunctor R.obj x).map_comp f g)

end

end OAI.AlgebraicGeometry.Comparison.Betti.PointModuleFunctor.Local
