import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Sites.Limits

/-! # Sheaf Closed Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport

noncomputable section

/-!
# Sections of a module sheaf with closed support

For an open subset `O`, the closed support is its complement. The sheaf of
sections supported there is the actual kernel of restriction to `O` and
pushforward to the ambient space. Its sections have exactly the expected
vanishing condition, and it is flasque whenever the original sheaf is flasque.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cohomology

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- Intersection with the open complement of the prescribed closed support. -/
def supportOpenIntersection (O : Opens X) : Opens X ⥤ Opens X where
  obj U := U ⊓ O
  map i := homOfLE (inf_le_inf_right O (leOfHom i))

/-- The actual restriction-pushforward presheaf has sections `F(U ∩ O)`. -/
def openRestrictionPushforwardPresheafIso (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) O.inclusion').obj
      ((O.sheafRestrict (C := ModuleCat.{0} R)).obj F)).obj ≅
        (supportOpenIntersection O).op ⋙ F.obj :=
  NatIso.ofComponents
    (fun U => F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf O U.unop))))
    (by
      intro U V i
      dsimp [supportOpenIntersection]
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1)

/-- The restriction-pushforward sheaf, written with literal intersection opens. -/
def openRestrictionPushforwardSheaf (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) : TopCat.Sheaf (ModuleCat.{0} R) X :=
  ⟨(supportOpenIntersection O).op ⋙ F.obj,
    TopCat.Presheaf.isSheaf_of_iso (openRestrictionPushforwardPresheafIso O F)
      (((TopCat.Sheaf.pushforward (ModuleCat.{0} R) O.inclusion').obj
        ((O.sheafRestrict (C := ModuleCat.{0} R)).obj F)).property)⟩

/-- The intersection description is canonically the usual `j_* (F|O)`. -/
def openRestrictionPushforwardSheafIso (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} R) O.inclusion').obj
      ((O.sheafRestrict (C := ModuleCat.{0} R)).obj F) ≅
        openRestrictionPushforwardSheaf O F :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    (ModuleCat.{0} R)).preimageIso (openRestrictionPushforwardPresheafIso O F)

/-- Restriction followed by pushforward acts on actual sheaf morphisms. -/
def openRestrictionPushforwardFunctor (O : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X where
  obj F := openRestrictionPushforwardSheaf O F
  map f := ⟨Functor.whiskerLeft (supportOpenIntersection O).op f.hom⟩

instance openRestrictionPushforwardFunctor_additive (O : Opens X) :
    (openRestrictionPushforwardFunctor (R := R) O).Additive where
  map_add := rfl

/-- Restriction from `F(U)` to `F(U ∩ O)`. -/
def sheafRestrictionToOpen (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    F ⟶ openRestrictionPushforwardSheaf O F :=
  ⟨{ app U := F.obj.map (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op
     naturality U V i := by
       dsimp [openRestrictionPushforwardSheaf, supportOpenIntersection]
       rw [← F.obj.map_comp, ← F.obj.map_comp]
       congr 1 }⟩

/-- The restriction maps form a natural transformation on sheaves. -/
def sheafRestrictionToOpenNatTrans (O : Opens X) :
    𝟭 (TopCat.Sheaf (ModuleCat.{0} R) X) ⟶ openRestrictionPushforwardFunctor O where
  app F := sheafRestrictionToOpen O F
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (f.hom.naturality (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op).symm

/-- The sheaf of sections supported in the closed set `X \ O`. -/
def closedSupportSheaf (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) : TopCat.Sheaf (ModuleCat.{0} R) X :=
  kernel (sheafRestrictionToOpen O F)

/-- Include the supported sheaf into the original sheaf. -/
def closedSupportSheafInclusion (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) : closedSupportSheaf O F ⟶ F :=
  kernel.ι (sheafRestrictionToOpen O F)

/-- Evaluation of a module sheaf on a specified open subset. -/
def moduleSheafSections (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op U)

instance moduleSheafSections_additive (U : Opens X) :
    (moduleSheafSections (R := R) U).Additive where
  map_add := rfl

instance moduleSheafSections_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (moduleSheafSections (R := R) U) := by
  have : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)) :=
    CategoryTheory.Sheaf.instPreservesFiniteLimitsFunctorOppositeSheafToPresheafOfHasFiniteLimits
  exact comp_preservesFiniteLimits _ _

/-- The inclusion's image is exactly the sections vanishing on `U ∩ O`. -/
theorem closedSupportSheafInclusion_range (O U : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    LinearMap.range (((closedSupportSheafInclusion O F).hom.app (op U)).hom) =
      LinearMap.ker ((F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op).hom) := by
  have h := (ShortComplex.kernelSequence_exact (sheafRestrictionToOpen O F)).map_of_mono_of_preservesKernel
    (moduleSheafSections U) inferInstance inferInstance
  exact h.moduleCat_range_eq_ker

/-- A supported section vanishes on the open complement by construction. -/
theorem closedSupportSheafInclusion_vanishes (O U : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X)
    (s : (closedSupportSheaf O F).obj.obj (op U)) :
    F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op
      ((closedSupportSheafInclusion O F).hom.app (op U) s) = 0 := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op U)) (kernel.condition (sheafRestrictionToOpen O F))) s
  exact h

/-- Inclusion of supported sections is injective on every open set. -/
theorem closedSupportSheafInclusion_injective (O U : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Function.Injective ((closedSupportSheafInclusion O F).hom.app (op U)) := by
  change Function.Injective
    ((moduleSheafSections U).map (kernel.ι (sheafRestrictionToOpen O F)))
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

end Cohomology

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport
