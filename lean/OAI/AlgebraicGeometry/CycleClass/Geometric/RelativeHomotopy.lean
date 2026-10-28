import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent
import OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! # Relative Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles

noncomputable section

/-!
# Homotopy invariance for genuine relative singular chains

A continuous homotopy of pairs restricts to an actual homotopy on their
subspaces. The compatible absolute singular-chain homotopies descend through
the cokernel defining relative chains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

variable {X Y : TopCat.{0}} {f g : X ⟶ Y} {A : Set X} {B : Set Y}

/-- The initial map of a homotopy preserving the subspaces is a map of pairs. -/
theorem homotopy_start_mapsTo (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Set.MapsTo f A B := by
  intro x hx
  exact (H.map_zero_left x) ▸ hH 0 hx

/-- The terminal map of a homotopy preserving the subspaces is a map of pairs. -/
theorem homotopy_end_mapsTo (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Set.MapsTo g A B := by
  intro x hx
  exact (H.map_one_left x) ▸ hH 1 hx

/-- Restriction of an actual homotopy of pairs to the subspaces. -/
def subspaceHomotopy (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    TopCat.Homotopy (LocalHomology.Cycles.subspaceMap f hf) (LocalHomology.Cycles.subspaceMap g hg) where
  toFun p := ⟨H (p.1, p.2.val), hH p.1 p.2.property⟩
  continuous_toFun :=
    (H.continuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (H.map_zero_left x.val)
  map_one_left x := Subtype.ext (H.map_one_left x.val)

@[simp]
theorem subspaceHomotopy_apply (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B)
    (t : unitInterval) (x : A) :
    (subspaceHomotopy hf hg H hH (t, x)).val = H (t, x.val) := rfl

/-- The square of actual homotopy maps commutes with the subspace inclusions. -/
theorem subspaceHomotopy_square (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    (LocalHomology.Cycles.subspaceInclusion X A ▷ TopCat.I) ≫ H.h =
      (subspaceHomotopy hf hg H hH).h ≫ LocalHomology.Cycles.subspaceInclusion Y B := by
  ext p
  rfl

/-- The actual singular-chain homotopy commutes with the actual inclusions
of the subspaces, by naturality of its prism construction. -/
theorem singularHomotopy_subspace_naturality
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f a ≫
        (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom a b =
      ((subspaceHomotopy hf hg H hH).singularChainComplexFunctorObjMap
        (ModuleCat.of ℤ ℤ)).hom a b ≫ (LocalHomology.Cycles.subspaceChainInclusion Y B).f b :=
  OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality.topologicalHomotopy_chain_naturality H (subspaceHomotopy hf hg H hH)
    (LocalHomology.Cycles.subspaceInclusion X A) (LocalHomology.Cycles.subspaceInclusion Y B)
    (subspaceHomotopy_square hf hg H hH) (ModuleCat.of ℤ ℤ) a b

/-- The ambient homotopy vanishes on subspace chains after relative projection. -/
theorem singularHomotopy_subspace_projection_zero
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f a ≫
        (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom a b ≫
        (LocalHomology.Cycles.relativeChainProjection Y B).f b = 0 := by
  have hz : (LocalHomology.Cycles.subspaceChainInclusion Y B).f b ≫
      (LocalHomology.Cycles.relativeChainProjection Y B).f b = 0 :=
    HomologicalComplex.congr_hom (LocalHomology.Cycles.subspaceChainInclusion_projection Y B) b
  rw [← Category.assoc, singularHomotopy_subspace_naturality hf hg H hH,
    Category.assoc, hz, comp_zero]

/-- A continuous homotopy of pairs induces a genuine homotopy between
their induced maps on the relative singular-chain complexes. -/
def relativeSingularChainsHomotopy
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Homotopy (LocalHomology.Cycles.relativeSingularChainsMap f hf) (LocalHomology.Cycles.relativeSingularChainsMap g hg) :=
  CokernelHomotopyDescent.Cycles.descendHomotopy (LocalHomology.Cycles.relativeChainSequence X A) (LocalHomology.Cycles.relativeChainSequence Y B)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (LocalHomology.Cycles.relativeChainProjection_naturality f hf) (LocalHomology.Cycles.relativeChainProjection_naturality g hg)
    (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ))
    (singularHomotopy_subspace_projection_zero hf hg H hH)

/-- Projection of the constructed relative homotopy agrees with the actual
absolute singular-chain homotopy. -/
@[reassoc]
theorem relativeSingularChainsHomotopy_projection
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (LocalHomology.Cycles.relativeChainProjection X A).f a ≫
        (relativeSingularChainsHomotopy hf hg H hH).hom a b =
      (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom a b ≫
        (LocalHomology.Cycles.relativeChainProjection Y B).f b :=
  CokernelHomotopyDescent.Cycles.descendHomotopy_projection (LocalHomology.Cycles.relativeChainSequence X A) (LocalHomology.Cycles.relativeChainSequence Y B)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (LocalHomology.Cycles.relativeChainProjection_naturality f hf) (LocalHomology.Cycles.relativeChainProjection_naturality g hg)
    (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ))
    (singularHomotopy_subspace_projection_zero hf hg H hH) a b

/-- Homotopic maps of pairs induce the same map on genuine relative
singular homology in every degree. -/
theorem relativeSingularHomologyMap_eq_of_homotopy
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap f hf n = LocalHomology.Cycles.relativeSingularHomologyMap g hg n :=
  (relativeSingularChainsHomotopy hf hg H hH).homologyMap_eq n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles
