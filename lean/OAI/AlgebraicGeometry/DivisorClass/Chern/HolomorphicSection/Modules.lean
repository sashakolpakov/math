import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing
import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! # Modules -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Modules

noncomputable section

/-! The constructed holomorphic sections form a module over the original holomorphic functions. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

instance holomorphicLineSection_functionSMul (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    SMul (Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) (Data.HolomorphicLineSection u U) where
  smul f s := ⟨fun i => Data.holomorphicOpenRestriction inf_le_left f * s.val i, by
    intro i j x hx hi hj
    change f ⟨x, hx⟩ * s.val j ⟨x, hx, hj⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ *
        (f ⟨x, hx⟩ * s.val i ⟨x, hx, hi⟩)
    rw [s.property i j x hx hi hj]
    ring⟩

@[simp]
theorem holomorphicLineSection_functionSMul_apply {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}
    {U : Opens M} (f : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) (s : Data.HolomorphicLineSection u U)
    (i : M) (x : ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)) :
    (f • s).val i x = f ⟨x.val, x.property.1⟩ * s.val i x := rfl

instance holomorphicLineSection_functionModule (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    Module (Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) (Data.HolomorphicLineSection u U) where
  one_smul s := by
    apply Data.holomorphicLineSection_ext
    intro i x
    exact one_mul _
  mul_smul f g s := by
    apply Data.holomorphicLineSection_ext
    intro i x
    exact mul_assoc _ _ _
  smul_zero f := by
    apply Data.holomorphicLineSection_ext
    intro i x
    exact mul_zero _
  smul_add f s t := by
    apply Data.holomorphicLineSection_ext
    intro i x
    exact mul_add _ _ _
  add_smul f g s := by
    apply Data.holomorphicLineSection_ext
    intro i x
    exact add_mul _ _ _
  zero_smul s := by
    apply Data.holomorphicLineSection_ext
    intro i x
    exact zero_mul _

theorem holomorphicLineSectionRestrict_functionSMul {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}
    {U V : Opens M} (h : V ≤ U) (f : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (s : Data.HolomorphicLineSection u U) :
    Data.holomorphicLineSectionRestrict h (f • s) =
      Data.holomorphicOpenRestriction h f • Data.holomorphicLineSectionRestrict h s := by
  apply Data.holomorphicLineSection_ext
  intro i x
  rfl

abbrev holomorphicStructureRingSheaf (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  (sheafCompose (Opens.grothendieckTopology M) (forget₂ CommRingCat RingCat)).obj (Holomorphic.Sheaves.holomorphicRingSheaf E M)

instance holomorphicLineSection_ringModule (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : (Opens M)ᵒᵖ) :
    Module ((holomorphicStructureRingSheaf E M).obj.obj U) (Data.HolomorphicLineSection u U.unop) :=
  holomorphicLineSection_functionModule u U.unop

def holomorphicLineSectionModulePresheaf (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    PresheafOfModules (holomorphicStructureRingSheaf E M).obj where
  obj U := ModuleCat.of _ (Data.HolomorphicLineSection u U.unop)
  map {U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((holomorphicStructureRingSheaf E M).obj.map f).hom).obj
      (ModuleCat.of _ (Data.HolomorphicLineSection u V.unop)))
    { toFun := Data.holomorphicLineSectionRestrict (leOfHom f.unop)
      map_add' := (Data.holomorphicLineSectionRestrict (leOfHom f.unop)).map_add
      map_smul' := holomorphicLineSectionRestrict_functionSMul (leOfHom f.unop) }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact Data.holomorphicLineSectionRestrict_self s
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (Data.holomorphicLineSectionRestrict_comp (leOfHom f.unop) (leOfHom g.unop) s).symm

theorem holomorphicLineSectionModulePresheaf_isSheaf (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    Presheaf.IsSheaf (Opens.grothendieckTopology M) (holomorphicLineSectionModulePresheaf u).presheaf := by
  change Presheaf.IsSheaf (Opens.grothendieckTopology M)
    ((Holomorphic.FunctionGluing.holomorphicLineSectionPresheaf u) ⋙ forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})
  exact ((sheafCompose (Opens.grothendieckTopology M)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (Holomorphic.FunctionGluing.holomorphicLineSectionSheaf u)).property

def holomorphicLineSectionModuleSheaf (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    SheafOfModules (holomorphicStructureRingSheaf E M) where
  val := holomorphicLineSectionModulePresheaf u
  isSheaf := holomorphicLineSectionModulePresheaf_isSheaf u

def holomorphicLineSectionFunctionLinearFrame (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    {U : Opens M} (i : M) (hU : U ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    Data.HolomorphicLineSection u U ≃ₗ[Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)]
      Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) where
  toFun := Data.holomorphicLineSectionFrameValue u i hU
  invFun := Data.holomorphicLineSectionOfFrame u i hU
  left_inv := Data.holomorphicLineSectionOfFrame_frameValue u i hU
  right_inv := Data.holomorphicLineSectionFrameValue_ofFrame u i hU
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Modules
