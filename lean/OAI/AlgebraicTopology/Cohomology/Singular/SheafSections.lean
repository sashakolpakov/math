import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomology
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
import OAI.AlgebraicTopology.Cohomology.Singular.Stalk
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Sheaf Sections -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafSections

noncomputable section

/-!
# Actual cohomology-sheaf sections from local cochain cohomology

For a complex of module sheaves, local cohomology maps canonically to sections
of its homology sheaf. This is a morphism of presheaves, so compatible local
classes give compatible sections, which glue uniquely in the actual sheaf.
No identification of local or global cohomology with sheaf sections is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R] {X : TopCat.{0}}

local instance sheafCohomologyForget_additive :
    (TopCat.Sheaf.forget (ModuleCat.{0} R) X).Additive where
  map_add := rfl

/-- Forget the sheaf condition degreewise, retaining the actual restriction maps. -/
def sheafUnderlyingCochainComplex
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ :=
  ((TopCat.Sheaf.forget (ModuleCat.{0} R) X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

/-- The presheaf of cohomology of the actual complexes of sections. -/
abbrev sheafSectionCohomologyPresheaf
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) (n : ℕ) :
    X.Presheaf (ModuleCat.{0} R) :=
  (sheafUnderlyingCochainComplex K).asFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- The canonical comparison from presheaf homology to underlying sheaf homology. -/
def sheafHomologyPresheafComparison
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) (n : ℕ) :
    (sheafUnderlyingCochainComplex K).homology n ⟶ (K.homology n).obj :=
  LeftExactHomology.leftExactHomologyComparison (K.sc n)
    (TopCat.Sheaf.forget (ModuleCat.{0} R) X)

/-- Local cochain cohomology maps to sections of the actual cohomology sheaf. -/
def sheafCohomologySectionComparison
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) (n : ℕ) :
    sheafSectionCohomologyPresheaf K n ⟶ (K.homology n).obj :=
  (Stalk.openCohomologyPresheafIso (sheafUnderlyingCochainComplex K) n).hom ≫
    sheafHomologyPresheafComparison K n

/-- The component of the canonical map on a specified open subset. -/
abbrev sheafCohomologySectionMap
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    (U : Opens X) (n : ℕ) :
    (Stalk.openCochainComplex (sheafUnderlyingCochainComplex K) U).homology n ⟶
      (K.homology n).obj.obj (op U) :=
  (sheafCohomologySectionComparison K n).app (op U)

/-- The comparison uses the actual homology projection, after evaluating the
underlying presheaf complex. -/
theorem sheafCohomologySectionMap_def
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    (U : Opens X) (n : ℕ) :
    sheafCohomologySectionMap K U n =
      (Stalk.openCohomologyIso (sheafUnderlyingCochainComplex K) U n).hom ≫
        (sheafHomologyPresheafComparison K n).app (op U) := rfl

@[reassoc]
theorem sheafCohomologySectionMap_naturality
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    (sheafSectionCohomologyPresheaf K n).map i.op ≫
        sheafCohomologySectionMap K U n =
      sheafCohomologySectionMap K V n ≫ (K.homology n).obj.map i.op :=
  (sheafCohomologySectionComparison K n).naturality i.op

/-- Compatible local cochain cohomology classes determine compatible sections
of the actual cohomology sheaf. -/
theorem sheafCohomologySectionMap_compatible
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    {ι : Type*} (U : ι → Opens X) (n : ℕ)
    (a : ∀ i, (sheafSectionCohomologyPresheaf K n).obj (op (U i)))
    (ha : TopCat.Presheaf.IsCompatible (sheafSectionCohomologyPresheaf K n) U a) :
    TopCat.Presheaf.IsCompatible (K.homology n).obj U
      (fun i => sheafCohomologySectionMap K (U i) n (a i)) := by
  intro i j
  change ((K.homology n).obj.map _)
      ((sheafCohomologySectionMap K (U i) n) (a i)) =
    ((K.homology n).obj.map _)
      ((sheafCohomologySectionMap K (U j) n) (a j))
  have hi := ConcreteCategory.congr_hom
    (sheafCohomologySectionMap_naturality K (Opens.infLELeft (U i) (U j)) n) (a i)
  have hj := ConcreteCategory.congr_hom
    (sheafCohomologySectionMap_naturality K (Opens.infLERight (U i) (U j)) n) (a j)
  exact hi.symm.trans ((congrArg (sheafCohomologySectionMap K (U i ⊓ U j) n)
    (ha i j)).trans hj)

/-- Compatible local cochain classes have a unique image section on the union.
This asserts gluing in the homology sheaf, not gluing in the cohomology presheaf. -/
theorem existsUnique_sheafCohomologySection
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    {ι : Type*} (U : ι → Opens X) (n : ℕ)
    (a : ∀ i, (sheafSectionCohomologyPresheaf K n).obj (op (U i)))
    (ha : TopCat.Presheaf.IsCompatible (sheafSectionCohomologyPresheaf K n) U a) :
    ∃! s : (K.homology n).obj.obj (op (iSup U)),
      ∀ i, (K.homology n).obj.map (Opens.leSupr U i).op s =
        sheafCohomologySectionMap K (U i) n (a i) :=
  (K.homology n).existsUnique_gluing U _ (sheafCohomologySectionMap_compatible K U n a ha)

/-- On an open cover, the image sections glue uniquely to a global section. -/
theorem existsUnique_global_sheafCohomologySection
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    {ι : Type*} (U : ι → Opens X) (hU : iSup U = ⊤) (n : ℕ)
    (a : ∀ i, (sheafSectionCohomologyPresheaf K n).obj (op (U i)))
    (ha : TopCat.Presheaf.IsCompatible (sheafSectionCohomologyPresheaf K n) U a) :
    ∃! s : (K.homology n).obj.obj (op (⊤ : Opens X)),
      ∀ i, (K.homology n).obj.map (homOfLE (le_top : U i ≤ ⊤)).op s =
        sheafCohomologySectionMap K (U i) n (a i) := by
  exact (K.homology n).existsUnique_gluing' U ⊤
    (fun i => homOfLE (le_top : U i ≤ ⊤)) (by rw [hU]) _
    (sheafCohomologySectionMap_compatible K U n a ha)

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafSections
