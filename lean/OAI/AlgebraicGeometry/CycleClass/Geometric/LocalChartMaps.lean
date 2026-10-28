import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology

/-! # Local Chart Maps -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalChartMaps

noncomputable section

section

/-!
# Actual local maps on chart neighborhoods

An injective continuous map induces a map of punctured pairs. These maps
compose on local singular homology. The chart isomorphism agrees with the
actual map on every subspace contained in its source; this permits comparison
on small coordinate balls.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable {X Y Z : TopCat.{0}}

/-- The local homology map induced by an injective continuous map. -/
def injectiveLocalHomologyMap (f : X ⟶ Y) (hf : Function.Injective f)
    (x : X) (n : ℕ) : LocalHomology.Cycles.localSingularHomology X x n ⟶ LocalHomology.Cycles.localSingularHomology Y (f x) n :=
  LocalHomology.Cycles.relativeSingularHomologyMap f (by
    intro z hz
    change z ≠ x at hz
    change f z ≠ f x
    exact fun h => hz (hf h)) n

/-- Actual local maps compose as the underlying continuous injections do. -/
@[reassoc]
theorem injectiveLocalHomologyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Injective f) (hg : Function.Injective g) (x : X) (n : ℕ) :
    injectiveLocalHomologyMap f hf x n ≫ injectiveLocalHomologyMap g hg (f x) n =
      injectiveLocalHomologyMap (f ≫ g) (hg.comp hf) x n :=
  LocalHomology.Cycles.relativeSingularHomologyMap_comp f g _ _ n

@[simp]
theorem injectiveLocalHomologyMap_id (x : X) (n : ℕ) :
    injectiveLocalHomologyMap (𝟙 X) Function.injective_id x n = 𝟙 _ :=
  LocalHomology.Cycles.relativeSingularHomologyMap_id X ({x}ᶜ : Set X) n

/-- The homeomorphism comparison is the actual map of punctured pairs. -/
theorem localSingularHomologyIso_hom (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    (LocalHomology.Cycles.localSingularHomologyIso e x n).hom =
      injectiveLocalHomologyMap (TopCat.isoOfHomeo e).hom e.injective x n := rfl

/-- The excision map itself is the local map of the continuous inclusion. -/
theorem localExcisionHomologyMap_eq_injective (X : TopCat.{0})
    (U : Set X) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X U x hx) n =
      injectiveLocalHomologyMap (LocalHomology.Cycles.subspaceInclusion X U) Subtype.val_injective
        (⟨x, hx⟩ : U) n := rfl

/-- A partial homeomorphism is a genuine continuous injection on its source. -/
def openPartialSourceMap (e : OpenPartialHomeomorph X Y) : TopCat.of e.source ⟶ Y :=
  (TopCat.isoOfHomeo e.toHomeomorphSourceTarget).hom ≫ LocalHomology.Cycles.subspaceInclusion Y e.target

theorem openPartialSourceMap_injective (e : OpenPartialHomeomorph X Y) :
    Function.Injective (openPartialSourceMap e) :=
  Subtype.val_injective.comp e.toHomeomorphSourceTarget.injective

@[simp]
theorem openPartialSourceMap_apply (e : OpenPartialHomeomorph X Y) (x : e.source) :
    openPartialSourceMap e x = e x := rfl

/-- The actual map obtained by restricting a partial homeomorphism to any
subspace lying in its source. -/
def openPartialRestrictionMap (e : OpenPartialHomeomorph X Y)
    (U : Set X) (hU : U ⊆ e.source) : TopCat.of U ⟶ Y :=
  LocalHomology.Cycles.subspaceMap (𝟙 X) (fun _ hu => hU hu) ≫ openPartialSourceMap e

theorem openPartialRestrictionMap_injective (e : OpenPartialHomeomorph X Y)
    (U : Set X) (hU : U ⊆ e.source) :
    Function.Injective (openPartialRestrictionMap e U hU) := by
  intro a b hab
  apply Subtype.ext
  exact e.injOn (hU a.property) (hU b.property) hab

@[simp]
theorem openPartialRestrictionMap_apply (e : OpenPartialHomeomorph X Y)
    (U : Set X) (hU : U ⊆ e.source) (x : U) :
    openPartialRestrictionMap e U hU x = e x := rfl

variable [T1Space X] [T1Space Y]

/-- The chart comparison agrees with the actual injective map on its
entire source, after the proved local excision map. -/
@[reassoc]
theorem openPartialLocalHomology_source (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) (n : ℕ) :
    HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X e.source x hx) n ≫
        (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x hx n).hom =
      injectiveLocalHomologyMap (openPartialSourceMap e)
        (openPartialSourceMap_injective e) (⟨x, hx⟩ : e.source) n := by
  rw [LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso_source, localSingularHomologyIso_hom,
    localExcisionHomologyMap_eq_injective]
  exact injectiveLocalHomologyMap_comp _ _ _ _ _ _

/-- Restricting to a smaller subspace does not change the chart's local
map. Openness of the smaller subspace is needed only to invert its excision
map, not for this commutative identity. -/
@[reassoc]
theorem openPartialLocalHomology_restriction (e : OpenPartialHomeomorph X Y)
    (U : Set X) (hU : U ⊆ e.source) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X U x hx) n ≫
        (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x (hU hx) n).hom =
      injectiveLocalHomologyMap (openPartialRestrictionMap e U hU)
        (openPartialRestrictionMap_injective e U hU) (⟨x, hx⟩ : U) n := by
  have hUinj : Function.Injective (LocalHomology.Cycles.subspaceMap (𝟙 X) (fun _ hu => hU hu)) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : e.source => z.val) hab)
  have hcomp :
      injectiveLocalHomologyMap (LocalHomology.Cycles.subspaceMap (𝟙 X) (fun _ hu => hU hu)) hUinj
          (⟨x, hx⟩ : U) n ≫
          HomologicalComplex.homologyMap
            (LocalExcision.Cycles.localExcisionChainMap X e.source x (hU hx)) n =
        HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X U x hx) n := by
    rw [localExcisionHomologyMap_eq_injective, localExcisionHomologyMap_eq_injective]
    exact injectiveLocalHomologyMap_comp _ _ _ _ _ _
  rw [← hcomp, Category.assoc, openPartialLocalHomology_source]
  exact injectiveLocalHomologyMap_comp _ _ _ _ _ _

end Cycles

end

/-!
# Local chart maps with specified base points

These wrappers make the equalities of actual base points explicit. This
allows ordinary maps of punctured pairs to be compared with chart
isomorphisms whose target point has been translated to zero.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable {X Y Z : TopCat.{0}}

/-- Equal continuous maps of the same pair induce equal relative homology
maps, independently of the proofs that they preserve the subspace. -/
theorem relativeSingularHomologyMap_congr {f g : X ⟶ Y}
    {A : Set X} {B : Set Y} (h : f = g)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap f hf n = LocalHomology.Cycles.relativeSingularHomologyMap g hg n := by
  subst g
  rfl

/-- Equality of the base points gives equality of the genuine local groups. -/
def localPointEqIso {x y : X} (h : x = y) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology X x n ≅ LocalHomology.Cycles.localSingularHomology X y n :=
  eqToIso (congrArg (fun z => LocalHomology.Cycles.localSingularHomology X z n) h)

/-- The map of punctured pairs for an injection with specified target point. -/
def injectiveLocalHomologyMapTo (f : X ⟶ Y) (hf : Function.Injective f)
    (x : X) (y : Y) (hxy : f x = y) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology X x n ⟶ LocalHomology.Cycles.localSingularHomology Y y n :=
  LocalHomology.Cycles.relativeSingularHomologyMap f (by
    intro z hz
    change z ≠ x at hz
    change f z ≠ y
    exact fun h => hz (hf (h.trans hxy.symm))) n

/-- Specifying the target point only transports the target of the same
actual homology map. -/
theorem injectiveLocalHomologyMap_pointEq (f : X ⟶ Y) (hf : Function.Injective f)
    (x : X) (y : Y) (hxy : f x = y) (n : ℕ) :
    injectiveLocalHomologyMap f hf x n ≫ (localPointEqIso hxy n).hom =
      injectiveLocalHomologyMapTo f hf x y hxy n := by
  subst y
  change injectiveLocalHomologyMap f hf x n ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- Specified-point local maps satisfy the usual composition law. -/
@[reassoc]
theorem injectiveLocalHomologyMapTo_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : X) (y : Y) (z : Z) (hxy : f x = y) (hyz : g y = z) (n : ℕ) :
    injectiveLocalHomologyMapTo f hf x y hxy n ≫
        injectiveLocalHomologyMapTo g hg y z hyz n =
      injectiveLocalHomologyMapTo (f ≫ g) (hg.comp hf) x z
        (by change g (f x) = z; rw [hxy]; exact hyz) n :=
  LocalHomology.Cycles.relativeSingularHomologyMap_comp f g _ _ n

/-- The first map of a composable pair, with its codomain restricted to
the source of the second. -/
def openPartialCompositionLift (e : OpenPartialHomeomorph X Y)
    (f : OpenPartialHomeomorph Y Z) :
    TopCat.of (e.trans f).source ⟶ TopCat.of f.source :=
  let r := openPartialRestrictionMap e (e.trans f).source (fun _ hu => hu.1)
  TopCat.ofHom ⟨fun u => ⟨r u, u.property.2⟩, r.hom.continuous.subtype_mk _⟩

theorem openPartialCompositionLift_injective (e : OpenPartialHomeomorph X Y)
    (f : OpenPartialHomeomorph Y Z) :
    Function.Injective (openPartialCompositionLift e f) := by
  intro a b hab
  apply Subtype.ext
  exact e.injOn a.property.1 b.property.1
    (congrArg (fun z : f.source => z.val) hab)

variable [T1Space X] [T1Space Y]

/-- The actual chart local isomorphism with a specified target point. -/
def openPartialLocalHomologyIsoTo (e : OpenPartialHomeomorph X Y)
    (x : X) (y : Y) (hx : x ∈ e.source) (hxy : e x = y) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology X x n ≅ LocalHomology.Cycles.localSingularHomology Y y n :=
  LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x hx n ≪≫ localPointEqIso hxy n

/-- The construction is unchanged when the actual partial homeomorphism
is unchanged; all proofs of its endpoint conditions are irrelevant. -/
theorem openPartialLocalHomologyIsoTo_congr
    {e f : OpenPartialHomeomorph X Y} (h : e = f)
    (x : X) (y : Y) (he : x ∈ e.source) (hf : x ∈ f.source)
    (hey : e x = y) (hfy : f x = y) (n : ℕ) :
    openPartialLocalHomologyIsoTo e x y he hey n =
      openPartialLocalHomologyIsoTo f x y hf hfy n := by
  subst f
  rfl

/-- The specified-point comparison agrees with the actual relative map
on every smaller subspace in the chart source. -/
@[reassoc]
theorem openPartialLocalHomologyIsoTo_restriction (e : OpenPartialHomeomorph X Y)
    (U : Set X) (hU : U ⊆ e.source) (x : X) (y : Y)
    (hx : x ∈ U) (hxy : e x = y) (n : ℕ) :
    HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X U x hx) n ≫
        (openPartialLocalHomologyIsoTo e x y (hU hx) hxy n).hom =
      injectiveLocalHomologyMapTo (openPartialRestrictionMap e U hU)
        (openPartialRestrictionMap_injective e U hU) (⟨x, hx⟩ : U) y hxy n := by
  change HomologicalComplex.homologyMap _ n ≫
    ((LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x (hU hx) n).hom ≫
      (localPointEqIso hxy n).hom) = _
  rw [← Category.assoc, openPartialLocalHomology_restriction,
    injectiveLocalHomologyMap_pointEq]

/-- The specified-point chart comparison on its whole source. -/
@[reassoc]
theorem openPartialLocalHomologyIsoTo_source (e : OpenPartialHomeomorph X Y)
    (x : X) (y : Y) (hx : x ∈ e.source) (hxy : e x = y) (n : ℕ) :
    HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X e.source x hx) n ≫
        (openPartialLocalHomologyIsoTo e x y hx hxy n).hom =
      injectiveLocalHomologyMapTo (openPartialSourceMap e)
        (openPartialSourceMap_injective e) (⟨x, hx⟩ : e.source) y hxy n := by
  change HomologicalComplex.homologyMap _ n ≫
    ((LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x hx n).hom ≫
      (localPointEqIso hxy n).hom) = _
  rw [← Category.assoc, openPartialLocalHomology_source,
    injectiveLocalHomologyMap_pointEq]

/-- When a local homeomorphism agrees with an actual global injection on
its source, its local action is the action of that injection. -/
theorem openPartialLocalHomologyIsoTo_eq_map
    (e : OpenPartialHomeomorph X Y) (f : X ⟶ Y) (hf : Function.Injective f)
    (x : X) (y : Y) (hx : x ∈ e.source) (hxy : e x = y) (hfx : f x = y)
    (heq : ∀ u ∈ e.source, e u = f u) (n : ℕ) :
    (openPartialLocalHomologyIsoTo e x y hx hxy n).hom =
      injectiveLocalHomologyMapTo f hf x y hfx n := by
  let i := LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n
  apply (cancel_epi i.hom).mp
  change HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X e.source x hx) n ≫ _ =
    HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X e.source x hx) n ≫ _
  rw [openPartialLocalHomologyIsoTo_source]
  change _ = injectiveLocalHomologyMapTo (LocalHomology.Cycles.subspaceInclusion X e.source)
    Subtype.val_injective (⟨x, hx⟩ : e.source) x rfl n ≫
      injectiveLocalHomologyMapTo f hf x y hfx n
  rw [injectiveLocalHomologyMapTo_comp]
  have hm : openPartialSourceMap e = LocalHomology.Cycles.subspaceInclusion X e.source ≫ f := by
    ext u
    exact heq u.val u.property
  unfold injectiveLocalHomologyMapTo
  exact relativeSingularHomologyMap_congr hm _ _ n

/-- The identity on an open source acts identically on local homology. -/
theorem openPartialLocalHomologyIsoTo_eq_id (e : OpenPartialHomeomorph X X)
    (x : X) (hx : x ∈ e.source) (heq : ∀ u ∈ e.source, e u = u) (n : ℕ) :
    (openPartialLocalHomologyIsoTo e x x hx (heq x hx) n).hom = 𝟙 _ := by
  rw [openPartialLocalHomologyIsoTo_eq_map e (𝟙 X) Function.injective_id
    x x hx (heq x hx) rfl heq n]
  exact LocalHomology.Cycles.relativeSingularHomologyMap_id X ({x}ᶜ : Set X) n

variable [T1Space Z]

/-- The isomorphisms induced by genuine pointed local homeomorphisms
compose. The proof uses the actual map on their common source. -/
@[reassoc]
theorem openPartialLocalHomologyIsoTo_comp
    (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
    (x : X) (y : Y) (z : Z) (hx : x ∈ e.source) (hy : y ∈ f.source)
    (hxy : e x = y) (hyz : f y = z) (n : ℕ) :
    (openPartialLocalHomologyIsoTo e x y hx hxy n).hom ≫
        (openPartialLocalHomologyIsoTo f y z hy hyz n).hom =
      (openPartialLocalHomologyIsoTo (e.trans f) x z
        ⟨hx, by change e x ∈ f.source; rw [hxy]; exact hy⟩
        (by change f (e x) = z; rw [hxy]; exact hyz) n).hom := by
  let U := (e.trans f).source
  have hU : U ⊆ e.source := fun _ hu => hu.1
  have hxU : x ∈ U := ⟨hx, by change e x ∈ f.source; rw [hxy]; exact hy⟩
  let i := LocalExcision.Cycles.localExcisionHomologyIso X U x hxU (e.trans f).open_source n
  apply (cancel_epi i.hom).mp
  change HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X U x hxU) n ≫
      (_ ≫ _) = HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X U x hxU) n ≫ _
  rw [← Category.assoc, openPartialLocalHomologyIsoTo_restriction e U hU,
    openPartialLocalHomologyIsoTo_restriction (e.trans f) U (Set.Subset.refl U)]
  have hlift : openPartialCompositionLift e f (⟨x, hxU⟩ : U) = (⟨y, hy⟩ : f.source) :=
    Subtype.ext hxy
  have hfactor :
      injectiveLocalHomologyMapTo (openPartialCompositionLift e f)
          (openPartialCompositionLift_injective e f) (⟨x, hxU⟩ : U)
          (⟨y, hy⟩ : f.source) hlift n ≫
        HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap Y f.source y hy) n =
      injectiveLocalHomologyMapTo (openPartialRestrictionMap e U hU)
        (openPartialRestrictionMap_injective e U hU) (⟨x, hxU⟩ : U) y hxy n := by
    change injectiveLocalHomologyMapTo _ _ _ _ _ _ ≫
      injectiveLocalHomologyMapTo (LocalHomology.Cycles.subspaceInclusion Y f.source) Subtype.val_injective
        (⟨y, hy⟩ : f.source) y rfl n = _
    exact injectiveLocalHomologyMapTo_comp _ _ _ _ _ _ _ _ _ _
  rw [← hfactor, Category.assoc, openPartialLocalHomologyIsoTo_source]
  exact injectiveLocalHomologyMapTo_comp _ _ _ _ _ _ _ _ _ _

/-- Inverting an actual local homeomorphism inverts its local homology
isomorphism. -/
theorem openPartialLocalHomologyIsoTo_symm_hom
    (e : OpenPartialHomeomorph X Y) (x : X) (y : Y)
    (hx : x ∈ e.source) (hxy : e x = y) (n : ℕ) :
    (openPartialLocalHomologyIsoTo e.symm y x
      (by change y ∈ e.target; rw [← hxy]; exact e.map_source hx)
      (by rw [← hxy]; exact e.left_inv hx) n).hom =
        (openPartialLocalHomologyIsoTo e x y hx hxy n).inv := by
  apply (cancel_epi (openPartialLocalHomologyIsoTo e x y hx hxy n).hom).mp
  rw [openPartialLocalHomologyIsoTo_comp, Iso.hom_inv_id]
  exact openPartialLocalHomologyIsoTo_eq_id (e.trans e.symm) x _
    (fun u hu => e.left_inv hu.1) n

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalChartMaps
