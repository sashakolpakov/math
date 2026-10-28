import OAI.AlgebraicTopology.Cohomology.Singular.SheafGluing
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes

/-! # Supported Cohomology Sections -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedCohomologySections

noncomputable section

/-!
# Gluing sections of the actual supported cohomology sheaf

The sheaf is the homology of the genuine kernel of restriction to the open
complement of the support. Local cochain classes map to its sections by the
canonical left-exact comparison. Agreement of their image germs suffices for
unique gluing, and the proved vanishing outside the support supplies zero on
the complementary open set.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cohomology

variable {R : Type} [Ring R]

/-- The actual cohomology sheaf of the supported singular sheaf complex. -/
abbrev supportedSingularCohomologySheaf (M : ModuleCat.{0} R) (X : TopCat.{0})
    (O : Opens X) (n : ℕ) : TopCat.Sheaf (ModuleCat.{0} R) X :=
  (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n

/-- A local class in the supported section complex determines a section of
the actual supported cohomology sheaf. -/
def supportedCohomologySectionMap (M : ModuleCat.{0} R) (X : TopCat.{0})
    (O U : Opens X) (n : ℕ) :
    (SupportStalkVanishes.Cohomology.supportedSingularSheafSections M X O U).homology n ⟶
      (supportedSingularCohomologySheaf M X O n).obj.obj (op U) :=
  AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) U n

@[reassoc]
theorem supportedCohomologySectionMap_naturality
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (O : Opens X)
    {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    HomologicalComplex.homologyMap (SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsRestriction M X O i) n ≫
        supportedCohomologySectionMap M X O U n =
      supportedCohomologySectionMap M X O V n ≫
        (supportedSingularCohomologySheaf M X O n).obj.map i.op :=
  AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap_naturality (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) i n

/-- Compatible image germs of local supported classes on a cover of the
closed support glue uniquely, with zero on its open complement. The
outside-support vanishing is proved, not supplied as a hypothesis. -/
theorem existsUnique_supportedCohomologySection_of_germs
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (O : Opens X)
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U ⊔ O = ⊤) (n : ℕ)
    (a : ∀ i, (SupportStalkVanishes.Cohomology.supportedSingularSheafSections M X O (U i)).homology n)
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (supportedSingularCohomologySheaf M X O n).presheaf.germ (U i) x hi
          (supportedCohomologySectionMap M X O (U i) n (a i)) =
        (supportedSingularCohomologySheaf M X O n).presheaf.germ (U j) x hj
          (supportedCohomologySectionMap M X O (U j) n (a j))) :
    ∃! s : (supportedSingularCohomologySheaf M X O n).obj.obj (op (⊤ : Opens X)),
      (∀ i, (supportedSingularCohomologySheaf M X O n).obj.map
          (homOfLE (le_top : U i ≤ ⊤)).op s =
        supportedCohomologySectionMap M X O (U i) n (a i)) ∧
      (supportedSingularCohomologySheaf M X O n).obj.map
        (homOfLE (le_top : O ≤ ⊤)).op s = 0 :=
  AlgebraicTopology.Cohomology.Singular.SheafGluing.existsUnique_moduleSheafSection_with_zero
    (supportedSingularCohomologySheaf M X O n) O U hcover
    (fun i => supportedCohomologySectionMap M X O (U i) n (a i)) ha
    (fun x hx => SupportStalkVanishes.Cycles.supportedSingularSheaf_cohomologySheaf_stalk_isZero_of_mem
      M O x hx n)

end Cohomology

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedCohomologySections
