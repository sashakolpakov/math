import OAI.AlgebraicTopology.Cohomology.Singular.SheafSections

/-! # Sheaf Section Stalk -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafSectionStalk

noncomputable section

/-!
# Section cohomology and the actual stalk complex

The cohomology of a stalk complex is the stalk of the presheaf of cohomology
of actual open-section complexes. This uses exactness of filtered module
colimits; it does not require the open-section functor to be exact. The
isomorphism is characterized by the actual cochain germs.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] {X : TopCat.{0}}
  (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)

/-- The degreewise genuine germ from sections on a neighborhood to a stalk. -/
def sheafSectionCochainGerm (U : Opens X) (x : X) (hx : x ∈ U) :
    Stalk.openCochainComplex (SheafSections.sheafUnderlyingCochainComplex K) U ⟶
      SheafQuasiIso.sheafStalkCochainComplex K x :=
  Stalk.cochainGerm (SheafSections.sheafUnderlyingCochainComplex K) U x hx

/-- Restricting actual sections before taking a germ gives the same stalk map. -/
@[reassoc]
theorem sheafSectionCochainGerm_restrict {U V : Opens X} (i : U ⟶ V)
    (x : X) (hx : x ∈ U) :
    (SheafSections.sheafUnderlyingCochainComplex K).asFunctor.map i.op ≫
        sheafSectionCochainGerm K U x hx =
      sheafSectionCochainGerm K V x (i.le hx) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact germ_res ((SheafSections.sheafUnderlyingCochainComplex K).X n) i x hx

/-- This comparison uses filtered exactness at the stalk, without asserting
exactness of the functor of sections on an open subset. -/
def sheafSectionStalkCohomologyIso (x : X) (n : ℕ) :
    (SheafQuasiIso.sheafStalkCochainComplex K x).homology n ≅
      (SheafSections.sheafSectionCohomologyPresheaf K n).stalk x :=
  Stalk.stalkCohomologyIso (SheafSections.sheafUnderlyingCochainComplex K) x n ≪≫
    (stalkFunctor (ModuleCat.{0} R) x).mapIso
      (Stalk.openCohomologyPresheafIso (SheafSections.sheafUnderlyingCochainComplex K) n).symm

/-- Cohomology of the actual cochain germ becomes the actual germ of an
open-section cohomology class under the canonical stalk comparison. -/
@[reassoc]
theorem sheafSectionStalkCohomologyIso_germ
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap (sheafSectionCochainGerm K U x hx) n ≫
        (sheafSectionStalkCohomologyIso K x n).hom =
      (SheafSections.sheafSectionCohomologyPresheaf K n).germ U x hx := by
  change HomologicalComplex.homologyMap
      (Stalk.cochainGerm (SheafSections.sheafUnderlyingCochainComplex K) U x hx) n ≫
    ((Stalk.stalkCohomologyIso (SheafSections.sheafUnderlyingCochainComplex K) x n).hom ≫
      (stalkFunctor (ModuleCat.{0} R) x).map
        (Stalk.openCohomologyPresheafIso (SheafSections.sheafUnderlyingCochainComplex K) n).inv) = _
  rw [← Category.assoc, Stalk.cochainGerm_homology, Category.assoc,
    stalkFunctor_map_germ, ← Category.assoc]
  change (Stalk.openCohomologyIso (SheafSections.sheafUnderlyingCochainComplex K) U n).hom ≫
    (Stalk.openCohomologyIso (SheafSections.sheafUnderlyingCochainComplex K) U n).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

/-- The stalk target is literally the filtered colimit over shrinking
neighborhoods of their section cohomology groups. -/
def sheafSectionStalkColimitIso (x : X) (n : ℕ) :
    (SheafQuasiIso.sheafStalkCochainComplex K x).homology n ≅
      colimit ((OpenNhds.inclusion x).op ⋙ SheafSections.sheafSectionCohomologyPresheaf K n) :=
  sheafSectionStalkCohomologyIso K x n

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafSectionStalk
