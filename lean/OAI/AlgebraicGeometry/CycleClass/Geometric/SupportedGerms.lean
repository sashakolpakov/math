import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes

/-! # Supported Germs -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedGerms.Cycles

noncomputable section

/-!
# Detection of genuine supported cohomology-sheaf sections

A section of the cohomology sheaf of supported singular cochains is determined
by its germs on the support. The missing germs vanish by the existing theorem
for the actual supported stalk complex, not by an additional support axiom.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})
  (O U : Opens X) (n : ℕ)

/-- Every actual supported cohomology-sheaf germ outside the support is zero. -/
theorem supportedCohomologySection_germ_eq_zero_of_mem
    (s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.obj (op U))
    (x : X) (hxU : x ∈ U) (hxO : x ∈ O) :
    TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
      U x hxU s = 0 := by
  let : Subsingleton
      (((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).presheaf.stalk x) :=
    ModuleCat.subsingleton_of_isZero
      (SupportStalkVanishes.Cycles.supportedSingularSheaf_cohomologySheaf_stalk_isZero_of_mem M O x hxO n)
  exact Subsingleton.elim _ _

/-- Germs on the actual closed support determine each cohomology-sheaf
section on an arbitrary open set. -/
theorem supportedCohomologySection_ext_on_support
    (s t : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.obj (op U))
    (h : ∀ (x : X) (hxU : x ∈ U), x ∉ O →
      TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
          U x hxU s =
        TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
          U x hxU t) :
    s = t := by
  apply TopCat.Presheaf.section_ext ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n) U s t
  intro x hxU
  by_cases hxO : x ∈ O
  · rw [supportedCohomologySection_germ_eq_zero_of_mem M X O U n s x hxU hxO,
      supportedCohomologySection_germ_eq_zero_of_mem M X O U n t x hxU hxO]
  · exact h x hxU hxO

/-- Scalar comparison can likewise be checked only at germs on the support. -/
theorem supportedCohomologySection_eq_smul_of_germs (q : R)
    (s t : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.obj (op U))
    (h : ∀ (x : X) (hxU : x ∈ U), x ∉ O →
      TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
          U x hxU t =
        q • TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
          U x hxU s) :
    t = q • s := by
  apply supportedCohomologySection_ext_on_support M X O U n t (q • s)
  intro x hxU hxO
  rw [map_smul]
  exact h x hxU hxO

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedGerms.Cycles
