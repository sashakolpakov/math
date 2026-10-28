import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultZeroKernelMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves
import OAI.Analysis.DifferentialForms.Manifold.SmoothFormD
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-! # Dolbeault Sheaf Maps -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultSheafMaps

noncomputable section

/-! Actual sheaf morphisms for the antiholomorphic differential and the original holomorphic inclusion. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def abelianOpenFormSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of E) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of E))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (Analysis.DifferentialForms.Manifold.SmoothFormD.smoothFormSheaf E n)

def openDolbeaultSheafMap (n : ℕ) : abelianOpenFormSheaf E n ⟶ abelianOpenFormSheaf E (n + 1) :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (DolbeaultOpen.openDolbeaultD (U := U.unop) n).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro form
      exact (DolbeaultZeroKernelMap.openDolbeaultD_restrict (leOfHom i.unop) form).symm }

def holomorphicToOpenZeroFormSheaf :
    Holomorphic.Sheaves.holomorphicFunctionSheaf E E ⟶ abelianOpenFormSheaf E 0 :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (DolbeaultZeroKernelMap.holomorphicZeroFormLinear U.unop).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro g
      exact (DolbeaultOpen.holomorphicFunctionZeroForm_restrict (leOfHom i.unop) g
        ((Holomorphic.Sheaves.holomorphicFunctionSheaf E E).obj.map i g) (fun _ => rfl)).symm }

theorem holomorphicToOpenZeroFormSheaf_mono : Mono (holomorphicToOpenZeroFormSheaf E) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mpr (DolbeaultZeroKernelMap.holomorphicZeroFormLinear_injective U.unop)

theorem holomorphicToOpenZeroFormSheaf_d :
    holomorphicToOpenZeroFormSheaf E ≫ openDolbeaultSheafMap E 0 = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro g
  exact DolbeaultZeroKernelMap.holomorphicZeroFormLinear_d U.unop g

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultSheafMaps
