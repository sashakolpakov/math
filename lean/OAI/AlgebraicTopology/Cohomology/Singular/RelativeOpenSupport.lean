import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Cohomology.Singular.Stalk

/-! # Relative Open Support -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

noncomputable section

section

/-!
# The presheaf of actual relative singular cochains

An open set `U` receives the kernel of the restriction from singular cochains
on `U` to cochains on `U ∩ A`. All restriction maps are induced by the actual
continuous inclusions of pairs. In applications with closed support `Z`, the
removed subset `A` is `Zᶜ`; no local vanishing or descent assertion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R]

/-- Identity maps of pairs act identically on relative singular cochains. -/
@[simp]
theorem relativeSingularCochainsMap_id (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    RelativeSequence.relativeSingularCochainsMap M (𝟙 X) (A := A) (B := A) (fun _ hx => hx) =
      𝟙 (RelativeSequence.relativeSingularCochains M X A) := by
  apply (cancel_mono (RelativeSequence.relativeCochainInclusion M X A)).mp
  rw [RelativeSequence.relativeCochainInclusion_naturality, Singular.Functor.singularPullback_id,
    Category.comp_id, Category.id_comp]

/-- Composition of maps of pairs gives the contravariant composition law on
the actual relative cochain kernels. -/
@[reassoc]
theorem relativeSingularCochainsMap_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    RelativeSequence.relativeSingularCochainsMap M g hg ≫ RelativeSequence.relativeSingularCochainsMap M f hf =
      RelativeSequence.relativeSingularCochainsMap M (f ≫ g) (fun _ hx => hg (hf hx)) := by
  apply (cancel_mono (RelativeSequence.relativeCochainInclusion M X A)).mp
  rw [Category.assoc, RelativeSequence.relativeCochainInclusion_naturality,
    ← Category.assoc, RelativeSequence.relativeCochainInclusion_naturality, Category.assoc,
    ← Singular.Functor.singularPullback_comp, RelativeSequence.relativeCochainInclusion_naturality]

/-- Identity maps of pairs act identically on relative cohomology. -/
@[simp]
theorem relativeSingularCohomologyMap_id (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    RelativeSequence.relativeSingularCohomologyMap M (𝟙 X) (A := A) (B := A) (fun _ hx => hx) n =
      𝟙 (RelativeSequence.relativeSingularCohomology M X A n) := by
  change HomologicalComplex.homologyMap _ n = _
  rw [relativeSingularCochainsMap_id, HomologicalComplex.homologyMap_id]

/-- Relative cohomology restrictions compose along the actual maps of pairs. -/
@[reassoc]
theorem relativeSingularCohomologyMap_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ) :
    RelativeSequence.relativeSingularCohomologyMap M g hg n ≫ RelativeSequence.relativeSingularCohomologyMap M f hf n =
      RelativeSequence.relativeSingularCohomologyMap M (f ≫ g) (fun _ hx => hg (hf hx)) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, relativeSingularCochainsMap_comp]

/-- Inverse maps of pairs give inverse maps on relative cochains. -/
theorem relativeSingularCochainsMap_comp_eq_id (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B A)
    (hfg : f ≫ g = 𝟙 X) :
    RelativeSequence.relativeSingularCochainsMap M g hg ≫ RelativeSequence.relativeSingularCochainsMap M f hf =
      𝟙 (RelativeSequence.relativeSingularCochains M X A) := by
  apply (cancel_mono (RelativeSequence.relativeCochainInclusion M X A)).mp
  rw [Category.assoc, RelativeSequence.relativeCochainInclusion_naturality,
    ← Category.assoc, RelativeSequence.relativeCochainInclusion_naturality, Category.assoc,
    ← Singular.Functor.singularPullback_comp, hfg, Singular.Functor.singularPullback_id,
    Category.comp_id, Category.id_comp]

/-- The removed subspace in an open set is the inverse image of the original
removed subset under the genuine subtype inclusion. -/
abbrev relativeOpenSubspace {X : TopCat.{0}} (A : Set X) (U : Opens X) : Set U :=
  {x | x.val ∈ A}

/-- Relative singular cochains on open subsets, with the subspace topology
and restriction along continuous inclusions of pairs. -/
def relativeCochainPresheaf (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    X.Presheaf (CochainComplex (ModuleCat.{0} R) ℕ) where
  obj U := RelativeSequence.relativeSingularCochains M (TopCat.of U.unop) (relativeOpenSubspace A U.unop)
  map f := RelativeSequence.relativeSingularCochainsMap M ((Opens.toTopCat X).map f.unop)
    (fun _ hx => hx)
  map_id U := by
    exact relativeSingularCochainsMap_id M (TopCat.of U.unop)
      (relativeOpenSubspace A U.unop)
  map_comp f g := by
    exact (relativeSingularCochainsMap_comp M
      ((Opens.toTopCat X).map g.unop) ((Opens.toTopCat X).map f.unop)
      (fun _ hx => hx) (fun _ hx => hx)).symm

/-- The degreewise relative singular cochain presheaf. -/
def relativeCochainDegreePresheaf (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) : X.Presheaf (ModuleCat.{0} R) :=
  relativeCochainPresheaf M X A ⋙
    HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- The presheaf of actual relative singular cohomology groups. -/
def relativeCohomologyPresheaf (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) : X.Presheaf (ModuleCat.{0} R) :=
  relativeCochainPresheaf M X A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n

@[simp]
theorem relativeCochainPresheaf_obj (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (U : Opens X) :
    (relativeCochainPresheaf M X A).obj (op U) =
      RelativeSequence.relativeSingularCochains M (TopCat.of U) (relativeOpenSubspace A U) := rfl

@[simp]
theorem relativeCochainPresheaf_map (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) {U V : Opens X} (i : U ⟶ V) :
    (relativeCochainPresheaf M X A).map i.op =
      RelativeSequence.relativeSingularCochainsMap M ((Opens.toTopCat X).map i)
        (A := relativeOpenSubspace A U) (B := relativeOpenSubspace A V)
        (fun _ hx => hx) := rfl

@[simp]
theorem relativeCochainDegreePresheaf_obj (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (U : Opens X) (n : ℕ) :
    (relativeCochainDegreePresheaf M X A n).obj (op U) =
      (RelativeSequence.relativeSingularCochains M (TopCat.of U) (relativeOpenSubspace A U)).X n := rfl

@[simp]
theorem relativeCohomologyPresheaf_obj (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (U : Opens X) (n : ℕ) :
    (relativeCohomologyPresheaf M X A n).obj (op U) =
      RelativeSequence.relativeSingularCohomology M (TopCat.of U) (relativeOpenSubspace A U) n := rfl

@[simp]
theorem relativeCohomologyPresheaf_map (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    (relativeCohomologyPresheaf M X A n).map i.op =
      RelativeSequence.relativeSingularCohomologyMap M ((Opens.toTopCat X).map i)
        (A := relativeOpenSubspace A U) (B := relativeOpenSubspace A V)
        (fun _ hx => hx) n := rfl

/-- The complex of module-valued presheaves formed by actual relative
singular cochains and their actual coboundaries. -/
def relativePresheafComplex (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ where
  X := relativeCochainDegreePresheaf M X A
  d i j :=
    { app := fun U => ((relativeCochainPresheaf M X A).obj U).d i j
      naturality := fun U V f => ((relativeCochainPresheaf M X A).map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext U
    exact ((relativeCochainPresheaf M X A).obj U).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact ((relativeCochainPresheaf M X A).obj U).d_comp_d i j k

@[simp]
theorem relativePresheafComplex_d_app (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (U : Opens X) (i j : ℕ) :
    ((relativePresheafComplex M X A).d i j).app (op U) =
      (RelativeSequence.relativeSingularCochains M (TopCat.of U) (relativeOpenSubspace A U)).d i j := rfl

/-- Forgetting the relative vanishing condition is natural on open sets. -/
def relativeCochainPresheafInclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    relativeCochainPresheaf M X A ⟶ DeRham.Comparison.SingularPresheaf.singularCochainPresheaf M X where
  app U := RelativeSequence.relativeCochainInclusion M (TopCat.of U.unop) (relativeOpenSubspace A U.unop)
  naturality U V f := RelativeSequence.relativeCochainInclusion_naturality M
    ((Opens.toTopCat X).map f.unop)
    (A := relativeOpenSubspace A V.unop) (B := relativeOpenSubspace A U.unop)
    (fun _ hx => hx)

/-- The actual inclusion of the relative complex into the absolute singular
cochain complex, now in the category of presheaves. -/
def relativePresheafInclusion (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    relativePresheafComplex M X A ⟶ DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X where
  f n := Functor.whiskerRight (relativeCochainPresheafInclusion M X A)
    (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n)
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact ((relativeCochainPresheafInclusion M X A).app U).comm i j

/-- The top open set recovers the genuine relative cochains of the original
pair. Both directions are induced by the canonical homeomorphism `⊤ ≅ X`. -/
def relativeCochainPresheafTopIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    (relativeCochainPresheaf M X A).obj (op ⊤) ≅ RelativeSequence.relativeSingularCochains M X A where
  hom := RelativeSequence.relativeSingularCochainsMap M (Opens.inclusionTopIso X).inv (fun _ hx => hx)
  inv := RelativeSequence.relativeSingularCochainsMap M (Opens.inclusionTopIso X).hom (fun _ hx => hx)
  hom_inv_id := relativeSingularCochainsMap_comp_eq_id M
    (Opens.inclusionTopIso X).hom (Opens.inclusionTopIso X).inv
    (fun _ hx => hx) (fun _ hx => hx) (Opens.inclusionTopIso X).hom_inv_id
  inv_hom_id := relativeSingularCochainsMap_comp_eq_id M
    (Opens.inclusionTopIso X).inv (Opens.inclusionTopIso X).hom
    (fun _ hx => hx) (fun _ hx => hx) (Opens.inclusionTopIso X).inv_hom_id

/-- The top-open cohomology is identified with actual relative singular
cohomology by the cohomology of the canonical pair isomorphism. -/
def relativeCohomologyPresheafTopIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (relativeCohomologyPresheaf M X A n).obj (op ⊤) ≅
      RelativeSequence.relativeSingularCohomology M X A n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (relativeCochainPresheafTopIso M X A)

/-- Taking cohomology objectwise agrees canonically with cohomology in the
category of module-valued presheaves. -/
def relativeCohomologyPresheafIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeCohomologyPresheaf M X A n ≅ (relativePresheafComplex M X A).homology n :=
  Stalk.openCohomologyPresheafIso (relativePresheafComplex M X A) n

end

/-!
# Relative cochains and restriction to the open complement

The subspace of `U` lying in an ambient open complement `O` is canonically
homeomorphic to the actual intersection open `U ⊓ O`. This identifies the
existing relative singular cochain complex with the kernel of ordinary
cochain restriction to that intersection. The comparison preserves the
actual inclusion into ordinary cochains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})

/-- Flattening the nested subtype identifies the removed subspace of an
open set with the actual intersection open. -/
def relativeOpenIntersectionHomeomorph (O U : Opens X) :
    relativeOpenSubspace (O : Set X) U ≃ₜ (U ⊓ O : Opens X) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)

/-- The actual restriction from cochains on `U` to cochains on `U ∩ O`. -/
abbrev openSupportCochainRestriction (O U : Opens X) :
    Basic.singularCochains M (TopCat.of U) ⟶ Basic.singularCochains M (TopCat.of (U ⊓ O : Opens X)) :=
  Singular.Functor.singularPullback M ((Opens.toTopCat X).map (homOfLE (inf_le_left : U ⊓ O ≤ U)))

/-- Pullback by the genuine flattening homeomorphism identifies the
cochains of the two presentations of the open complement in `U`. -/
def relativeOpenIntersectionCochainsIso (O U : Opens X) :
    Basic.singularCochains M (TopCat.of (relativeOpenSubspace (O : Set X) U)) ≅
      Basic.singularCochains M (TopCat.of (U ⊓ O : Opens X)) :=
  (Singular.Functor.singularCochainsFunctor M).mapIso
    (TopCat.isoOfHomeo (relativeOpenIntersectionHomeomorph X O U)).symm.op

/-- The flattening isomorphism preserves the actual restriction map. -/
theorem relativeOpenIntersectionCochainsIso_restriction (O U : Opens X) :
    RelativeSequence.subspaceCochainRestriction M (TopCat.of U) (relativeOpenSubspace (O : Set X) U) ≫
        (relativeOpenIntersectionCochainsIso X M O U).hom =
      openSupportCochainRestriction X M O U := by
  dsimp only [relativeOpenIntersectionCochainsIso, Functor.mapIso_hom,
    Iso.op_hom, Iso.symm_hom, RelativeSequence.subspaceCochainRestriction,
    openSupportCochainRestriction, Singular.Functor.singularPullback]
  rw [← Functor.map_comp]
  congr 1

/-- The existing relative cochain complex is canonically the actual
kernel of restriction to the open complement in this neighborhood. -/
def relativeOpenSupportKernelIso (O U : Opens X) :
    RelativeSequence.relativeSingularCochains M (TopCat.of U) (relativeOpenSubspace (O : Set X) U) ≅
      kernel (openSupportCochainRestriction X M O U) :=
  kernel.mapIso
    (RelativeSequence.subspaceCochainRestriction M (TopCat.of U) (relativeOpenSubspace (O : Set X) U))
    (openSupportCochainRestriction X M O U) (Iso.refl _)
    (relativeOpenIntersectionCochainsIso X M O U) (by
      simpa only [Iso.refl_hom, Category.id_comp] using
        relativeOpenIntersectionCochainsIso_restriction X M O U)

/-- The kernel identification acts as the identity on the ambient
ordinary cochain, so it preserves the intended relative class. -/
@[reassoc (attr := simp)]
theorem relativeOpenSupportKernelIso_inclusion (O U : Opens X) :
    (relativeOpenSupportKernelIso X M O U).hom ≫
        kernel.ι (openSupportCochainRestriction X M O U) =
      RelativeSequence.relativeCochainInclusion M (TopCat.of U) (relativeOpenSubspace (O : Set X) U) := by
  simp only [relativeOpenSupportKernelIso, kernel.mapIso_hom, kernel.lift_ι,
    Iso.refl_hom, Category.comp_id]

end

end OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport
