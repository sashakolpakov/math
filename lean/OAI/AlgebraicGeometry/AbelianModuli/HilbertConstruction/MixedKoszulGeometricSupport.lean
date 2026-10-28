import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleKoszulComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Topology.JacobsonSpace

/-! # Mixed Koszul Geometric Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulGeometricSupport

noncomputable section

/-! A mixed Koszul complex contracts at every field point away from
its common zero set. If that set is finite on a Jacobson scheme, its
pullback to a local spectrum is supported only at the closed point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

def mixedSectionZeroSet {X : Scheme.{u}} (bs : List (LineBundleKoszulComplex.LineBundleSection X)) : Set X :=
  {x | ∀ b ∈ bs, x ∉ Ample.LineBundles.sectionNonvanishing b.2}

theorem mixedSectionZeroSet_isClosed {X : Scheme.{u}} (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    IsClosed (mixedSectionZeroSet bs) := by
  have he : mixedSectionZeroSet bs = ⋂ b ∈ bs, (Ample.LineBundles.sectionNonvanishing b.2 : Set X)ᶜ := by
    ext x
    simp only [mixedSectionZeroSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, SetLike.mem_coe]
  rw [he]
  exact isClosed_iInter (fun b => isClosed_iInter (fun _ => (Ample.LineBundles.sectionNonvanishing b.2).isOpen.isClosed_compl))

local instance mixedSupportPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

theorem mixedKoszul_field_pullback_contractible
    {K : Type u} [Field K] {X : Scheme.{u}}
    (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (q : Spec (.of K) ⟶ X)
    (hq : q (IsLocalRing.closedPoint K) ∉ mixedSectionZeroSet bs) :
    Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℤ)).obj
      (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs))) 0) := by
  apply LineBundleKoszulComplex.mixedLineBundleKoszulComplex_pullback_contractible M bs q
  by_contra h
  apply hq
  intro b hb hnonvanishing
  have hp : IsIso (Ample.LineBundles.pullbackSection q b.2) := by
    apply (Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
    rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange q b.1 b.2]
    apply top_unique
    intro x _
    change q x ∈ Ample.LineBundles.sectionNonvanishing b.2
    have he : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact he.symm ▸ hnonvanishing
  exact h ⟨b, hb, (Section.Nonvanishing.isIso_pullbackSection_iff q b.2).mp hp⟩

theorem finiteClosedSet_subset_closedPoints
    {T : Type u} [TopologicalSpace T] [JacobsonSpace T]
    (C : Set T) (hC : IsClosed C) (hfinite : C.Finite) : C ⊆ closedPoints T := by
  let : Finite C := hfinite.to_subtype
  let : JacobsonSpace C := JacobsonSpace.of_isClosedEmbedding hC.isClosedEmbedding_subtypeVal
  let : DiscreteTopology C := inferInstance
  intro x hx
  have h := hC.isClosedEmbedding_subtypeVal.isClosedMap
    ({⟨x, hx⟩} : Set C) isClosed_singleton
  change IsClosed {x}
  simpa only [Set.image_singleton] using h

theorem finiteClosedSet_stalk_preimage_eq_closedPoint
    {X : Scheme.{u}} [JacobsonSpace X] (C : Set X) (hC : IsClosed C) (hfinite : C.Finite)
    (x : X) (y : Spec (X.presheaf.stalk x)) (hy : X.fromSpecStalk x y ∈ C) :
    y = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
  have hclosed : IsClosed {X.fromSpecStalk x y} := finiteClosedSet_subset_closedPoints C hC hfinite hy
  have hspec : X.fromSpecStalk x y ⤳ x := by
    have hr : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hr
    exact hr
  have he : x = X.fromSpecStalk x y := hspec.mem_closed hclosed (Set.mem_singleton _)
  apply (X.fromSpecStalk x).isEmbedding.injective
  rw [Scheme.fromSpecStalk_closedPoint]
  exact he.symm

theorem mixedKoszul_stalk_field_pullback_contractible
    {K : Type u} [Field K] {X : Scheme.{u}} [JacobsonSpace X]
    (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (hf : (mixedSectionZeroSet bs).Finite)
    (x : X) (q : Spec (.of K) ⟶ Spec (X.presheaf.stalk x))
    (hq : q (IsLocalRing.closedPoint K) ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)) :
    Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback (q ≫ X.fromSpecStalk x)).mapHomologicalComplex (.up ℤ)).obj
      (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs))) 0) := by
  apply mixedKoszul_field_pullback_contractible M bs (q ≫ X.fromSpecStalk x)
  intro h
  exact hq (finiteClosedSet_stalk_preimage_eq_closedPoint
    (mixedSectionZeroSet bs) (mixedSectionZeroSet_isClosed bs) hf x _ h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulGeometricSupport
