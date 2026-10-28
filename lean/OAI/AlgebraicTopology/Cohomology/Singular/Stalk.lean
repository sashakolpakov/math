import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Topology.Sheaves.Abelian

/-! # Stalk -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Stalk

noncomputable section

/-!
# Stalks of cochain complexes

The stalk of a module-valued presheaf is a filtered colimit of modules. Exactness
of filtered colimits gives the canonical comparison between the cohomology of
the stalk complex and the stalk of the cohomology presheaf. The comparison is
compatible with the actual germ morphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

variable {R : Type} [Ring R] {X : TopCat.{0}}

set_option backward.isDefEq.respectTransparency false in
/-- Filtered colimits of modules are left exact, so taking stalks preserves
finite limits of module-valued presheaves. -/
instance moduleStalk_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (stalkFunctor (ModuleCat.{0} R) x) := by
  let F : ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} R) ⥤ ((OpenNhds x)ᵒᵖ ⥤ ModuleCat.{0} R) :=
    (Functor.whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op
  exact comp_preservesFiniteLimits F (colim : ((OpenNhds x)ᵒᵖ ⥤ ModuleCat.{0} R) ⥤ _)

set_option backward.isDefEq.respectTransparency false in
/-- Taking stalks preserves finite colimits of module-valued presheaves. -/
instance moduleStalk_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (stalkFunctor (ModuleCat.{0} R) x) := by
  infer_instance

/-- Apply the actual stalk functor in each degree of a presheaf complex. -/
def stalkCochainComplex
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (x : X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  ((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The canonical isomorphism identifying stalk cohomology with the stalk of
the cohomology presheaf. -/
def stalkCohomologyIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (x : X) (n : ℕ) :
    (stalkCochainComplex K x).homology n ≅ (K.homology n).stalk x :=
  (K.sc n).mapHomologyIso (stalkFunctor (ModuleCat.{0} R) x)

/-- Evaluation of an actual module-valued presheaf on an open subset. -/
def presheafSectionFunctor (U : Opens X) : X.Presheaf (ModuleCat.{0} R) ⥤ ModuleCat.{0} R :=
  (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op U)

instance presheafSectionFunctor_additive (U : Opens X) :
    (presheafSectionFunctor (R := R) U).Additive where

instance presheafSectionFunctor_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (presheafSectionFunctor (R := R) U) :=
  inferInstanceAs
    (PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op U)))

instance presheafSectionFunctor_preservesFiniteColimits (U : Opens X) :
    PreservesFiniteColimits (presheafSectionFunctor (R := R) U) :=
  inferInstanceAs
    (PreservesFiniteColimits ((evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op U)))

/-- Evaluate a presheaf complex on an open subset. -/
def openCochainComplex
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (U : Opens X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  ((presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The canonical comparison between sectionwise cohomology and the sections
of the homology presheaf of a complex of presheaves. -/
def openCohomologyIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (U : Opens X) (n : ℕ) :
    (openCochainComplex K U).homology n ≅ (K.homology n).obj (op U) :=
  (K.sc n).mapHomologyIso (presheafSectionFunctor U)

/-- Germs are natural in the module-valued presheaf. -/
def presheafGerm (U : Opens X) (x : X) (hx : x ∈ U) :
    presheafSectionFunctor U ⟶
      stalkFunctor (ModuleCat.{0} R) x where
  app F := TopCat.Presheaf.germ F U x hx
  naturality _ _ f := (stalkFunctor_map_germ U x hx f).symm

/-- The morphism from the complex of sections to the complex of stalks induced
by the actual germ in every degree. -/
def cochainGerm
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ)
    (U : Opens X) (x : X) (hx : x ∈ U) :
    openCochainComplex K U ⟶ stalkCochainComplex K x :=
  ((presheafGerm (R := R) U x hx).mapHomologicalComplex (ComplexShape.up ℕ)).app K

@[simp]
theorem cochainGerm_f
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ)
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    (cochainGerm K U x hx).f n = (K.X n).germ U x hx := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Taking cohomology of a germ agrees with taking the germ of a cohomology
class under the two canonical homology comparison isomorphisms. -/
@[reassoc]
theorem cochainGerm_homology
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ)
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap (cochainGerm K U x hx) n ≫
        (stalkCohomologyIso K x n).hom =
      (openCohomologyIso K U n).hom ≫ (K.homology n).germ U x hx := by
  change ShortComplex.homologyMap ((K.sc n).mapNatTrans (presheafGerm (R := R) U x hx)) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [stalkCohomologyIso, openCohomologyIso, presheafGerm,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Stalk--cohomology comparison is natural in the presheaf complex. -/
@[reassoc]
theorem stalkCohomologyIso_naturality
    {K L : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ}
    (f : K ⟶ L) (x : X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex
          (ComplexShape.up ℕ)).map f) n ≫ (stalkCohomologyIso L x n).hom =
      (stalkCohomologyIso K x n).hom ≫
        (stalkFunctor (ModuleCat.{0} R) x).map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
    (stalkFunctor (ModuleCat.{0} R) x)

/-- Evaluation--cohomology comparison is natural in the presheaf complex. -/
@[reassoc]
theorem openCohomologyIso_naturality
    {K L : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ}
    (f : K ⟶ L) (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((presheafSectionFunctor U).mapHomologicalComplex
          (ComplexShape.up ℕ)).map f) n ≫ (openCohomologyIso L U n).hom =
      (openCohomologyIso K U n).hom ≫ (HomologicalComplex.homologyMap f n).app (op U) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
    (presheafSectionFunctor U)

set_option backward.isDefEq.respectTransparency false in
/-- The homology object in the presheaf category agrees canonically with
taking cohomology on every open set. -/
def openCohomologyPresheafIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (n : ℕ) :
    K.asFunctor ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        (ComplexShape.up ℕ) n ≅ K.homology n :=
  NatIso.ofComponents (fun U => openCohomologyIso K U.unop n) (fun {U V} f => by
    let τ : presheafSectionFunctor (R := R) U.unop ⟶ presheafSectionFunctor V.unop :=
      (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).map f
    change ShortComplex.homologyMap ((K.sc n).mapNatTrans τ) ≫ _ = _
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [openCohomologyIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

/-- Vanishing of the stalk of the cohomology presheaf is equivalent to
exactness of the actual stalk complex in that degree. -/
theorem stalkCohomology_isZero_iff
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (x : X) (n : ℕ) :
    IsZero ((K.homology n).stalk x) ↔ (stalkCochainComplex K x).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h => h.of_iso (stalkCohomologyIso K x n),
    fun h => h.of_iso (stalkCohomologyIso K x n).symm⟩

/-- Sectionwise ordinary singular cohomology is the homology presheaf of
the actual singular cochain presheaf complex. -/
def singularCohomologyPresheafIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    DeRham.Comparison.SingularPresheaf.singularCohomologyPresheaf M X n ≅
      (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).homology n :=
  openCohomologyPresheafIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) n

/-- Cohomology of the stalk complex of genuine singular cochains is the
stalk of the presheaf of ordinary singular cohomology groups. -/
def singularStalkCohomologyIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (x : X) (n : ℕ) :
    (stalkCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) x).homology n ≅
      (DeRham.Comparison.SingularPresheaf.singularCohomologyPresheaf M X n).stalk x :=
  stalkCohomologyIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) x n ≪≫
    (stalkFunctor (ModuleCat.{0} R) x).mapIso (singularCohomologyPresheafIso M X n).symm

set_option backward.isDefEq.respectTransparency false in
/-- The singular stalk comparison is characterized by the actual germs of
ordinary singular cohomology classes. -/
@[reassoc]
theorem singularStalkCohomologyIso_germ (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap
        (cochainGerm (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) U x hx) n ≫
        (singularStalkCohomologyIso M X x n).hom =
      (DeRham.Comparison.SingularPresheaf.singularCohomologyPresheaf M X n).germ U x hx := by
  change HomologicalComplex.homologyMap _ n ≫
    ((stalkCohomologyIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) x n).hom ≫
      (stalkFunctor (ModuleCat.{0} R) x).map (singularCohomologyPresheafIso M X n).inv) = _
  rw [← Category.assoc, cochainGerm_homology, Category.assoc,
    stalkFunctor_map_germ, ← Category.assoc]
  change (openCohomologyIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) U n).hom ≫
    (openCohomologyIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) U n).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicTopology.Cohomology.Singular.Stalk
