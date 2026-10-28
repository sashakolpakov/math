import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Sheafify

/-! # Sheaf Quasi Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

noncomputable section

/-!
# Quasi-isomorphisms of module sheaf complexes and stalks

The stalk functors on module sheaves are exact and jointly detect isomorphisms.
Consequently a morphism of complexes of sheaves is a quasi-isomorphism exactly
when it is a quasi-isomorphism on every stalk. The comparison with sheafified
presheaf complexes is induced by the actual sheafification unit in every degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

/-- Module limits exist in the carrier universe even when the scalars lie in
the smaller universe. -/
local instance sheafQuasiIsoModuleLimits :
    HasLimitsOfSize.{u,u} (ModuleCat.{u,0} R) :=
  ModuleCat.hasLimitsOfSize.{u,u,u,0}

/-- The complex formed by the actual stalks of a complex of module sheaves. -/
def sheafStalkCochainComplex
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ) (x : X) :
    CochainComplex (ModuleCat.{u,0} R) ℕ :=
  (((TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
    stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

/-- The morphism on actual stalk complexes induced by a sheaf complex morphism. -/
def sheafStalkCochainMap
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) (x : X) :
    sheafStalkCochainComplex K x ⟶ sheafStalkCochainComplex L x :=
  ((TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
    stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).map f

/-- Exactness of the sheaf stalk functor gives the canonical homology comparison. -/
def sheafStalkCohomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ) (x : X) (n : ℕ) :
    (sheafStalkCochainComplex K x).homology n ≅
      (TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
        stalkFunctor (ModuleCat.{u,0} R) x).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
    stalkFunctor (ModuleCat.{u,0} R) x)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk--cohomology comparison intertwines the genuine induced maps. -/
@[reassoc]
theorem sheafStalkCohomologyIso_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) (x : X) (n : ℕ) :
    HomologicalComplex.homologyMap (sheafStalkCochainMap f x) n ≫
        (sheafStalkCohomologyIso L x n).hom =
      (sheafStalkCohomologyIso K x n).hom ≫
        (stalkFunctor (ModuleCat.{u,0} R) x).map
          (HomologicalComplex.homologyMap f n).hom :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
    (TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙ stalkFunctor (ModuleCat.{u,0} R) x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A sheaf complex morphism induces an isomorphism in degree `n` exactly when
it does so on every actual stalk complex. -/
theorem sheaf_quasiIsoAt_iff_stalk
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    QuasiIsoAt f n ↔ ∀ x : X, QuasiIsoAt (sheafStalkCochainMap f x) n := by
  rw [quasiIsoAt_iff_isIso_homologyMap,
    TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  apply forall_congr'
  intro x
  rw [quasiIsoAt_iff_isIso_homologyMap]
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using
    (congrArg IsIso (sheafStalkCohomologyIso_naturality f x n)).to_iff.symm

/-- A morphism of module sheaf complexes is a quasi-isomorphism if and only
if the induced morphism of complexes at every stalk is a quasi-isomorphism. -/
theorem sheaf_quasiIso_iff_stalk
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) :
    QuasiIso f ↔ ∀ x : X, QuasiIso (sheafStalkCochainMap f x) := by
  simp only [quasiIso_iff, sheaf_quasiIsoAt_iff_stalk]
  exact forall_comm

/-- Apply the actual sheafification functor in every cochain degree. -/
def sheafifiedCochainComplex
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual sheafification unit induces a map from a presheaf stalk complex
to the stalk complex of its sheafification. -/
def sheafificationStalkComplexHom
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) :
    ((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K ⟶
      sheafStalkCochainComplex (sheafifiedCochainComplex K) x where
  f n := (stalkFunctor (ModuleCat.{u,0} R) x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n))
  comm' i j _ := by
    symm
    change (stalkFunctor (ModuleCat.{u,0} R) x).map (K.d i j) ≫
        (stalkFunctor (ModuleCat.{u,0} R) x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X j)) =
      (stalkFunctor (ModuleCat.{u,0} R) x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X i)) ≫
        (stalkFunctor (ModuleCat.{u,0} R) x).map
          (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (K.d i j))
    rw [← Functor.map_comp, ← Functor.map_comp,
      CategoryTheory.toSheafify_naturality]

/-- Sheafification preserves each stalk, so the induced map of stalk complexes
is already an isomorphism of complexes. -/
instance sheafificationStalkComplexHom_isIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) :
    IsIso (sheafificationStalkComplexHom K x) := by
  have : ∀ n : ℕ, IsIso ((sheafificationStalkComplexHom K x).f n) :=
    fun n => stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{u,0} R) (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical comparison of presheaf and sheafification stalk complexes,
whose forward map comes from the sheafification unit. -/
def sheafificationStalkComplexIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) :
    ((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K ≅
      sheafStalkCochainComplex (sheafifiedCochainComplex K) x :=
  asIso (sheafificationStalkComplexHom K x)

@[simp]
theorem sheafificationStalkComplexIso_hom_f
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) (n : ℕ) :
    (sheafificationStalkComplexIso K x).hom.f n =
      (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk comparison for sheafification is natural in the presheaf complex. -/
@[reassoc]
theorem sheafificationStalkComplexIso_naturality
    {K L : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ}
    (f : K ⟶ L) (x : X) :
    ((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map f ≫ (sheafificationStalkComplexIso L x).hom =
      (sheafificationStalkComplexIso K x).hom ≫
        sheafStalkCochainMap
          (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} R)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map f) x := by
  ext n : 1
  change (stalkFunctor (ModuleCat.{u,0} R) x).map (f.f n) ≫
      (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (L.X n)) =
    (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)) ≫
      (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (f.f n))
  rw [← Functor.map_comp, ← Functor.map_comp, CategoryTheory.toSheafify_naturality]

/-- The comparison sends the germ of a section to the germ of its actual image
under the sheafification unit. -/
theorem sheafificationStalkComplexIso_hom_germ
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ)
    (x : X) (n : ℕ) (U : Opens X) (hx : x ∈ U) (s : (K.X n).obj (op U)) :
    (sheafificationStalkComplexIso K x).hom.f n ((K.X n).germ U x hx s) =
      TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology X) (K.X n)) U x hx
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)).app (op U) s) :=
  stalkFunctor_map_germ_apply U x hx
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)) s

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sheafifying a morphism of module presheaf complexes gives a
quasi-isomorphism exactly when the original morphism is one on every stalk. -/
theorem sheafified_quasiIso_iff_stalk
    {K L : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ} (f : K ⟶ L) :
    QuasiIso (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f) ↔
      ∀ x : X, QuasiIso (((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map f) := by
  rw [sheaf_quasiIso_iff_stalk]
  apply forall_congr'
  intro x
  rw [← quasiIso_iff_comp_left (sheafificationStalkComplexIso K x).hom,
    ← sheafificationStalkComplexIso_naturality,
    quasiIso_iff_comp_right]

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
