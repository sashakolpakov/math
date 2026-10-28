import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.NestedPushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ReferenceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AmbientProducts

/-! # Pushforward Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.PushforwardCoordinates

noncomputable section

/-! The original ambient principal module class has the same image
as its source single-sheaf class, with the actual ordered pushforward
and all original single-degree coordinate isomorphisms retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category C] {A B D E L R : C}
    (a : A ⟶ B) (b : B ⟶ D) (e : D ⟶ E) (l : B ⟶ L)
    (m : A ⟶ L) (u : L ⟶ R) (r : R ⟶ E) (v : L ⟶ E)
    (hb : b ≫ e = l ≫ v) (hl : a ≫ l = m) (hv : u ≫ r = v) :
    a ≫ b ≫ e = m ≫ u ≫ r := by
  rw [hb, ← Category.assoc a l v, hl, ← hv]

variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U)
  {ι κ ν μ ρ : Type}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → Principal.SectionPresheaf.Index U)
  (B : κ → Z.Opens) (J : ν → Z.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι
    ((Principal.AdditiveSections.opens U hU).obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Z.Opens) (T : ρ → Z.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover ((Principal.AdditiveSections.opens U hU).obj (⊤_ _)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (N : Y.Modules) (c g : ℕ)

attribute [local instance] RelativeCech.ReindexData.preimage_limits
  Principal.CechPushforwardCoordinates.pulled_products
  Principal.NestedPushforward.ambient_plain_relative
  Principal.NestedPushforward.ambient_plain_ordered
  Principal.NestedPushforward.pushed_relative
  Principal.NestedPushforward.pushed_ordered
  Principal.NestedPushforward.source_plain_relative
  Principal.NestedPushforward.source_plain_ordered
  Principal.NestedPushforward.source_sheaf_relative
  Principal.NestedPushforward.source_sheaf_ordered
  Principal.NestedPushforward.source_mapped_relative
  Principal.NestedPushforward.source_mapped_ordered
  Principal.NestedPushforward.source_plain_raw_relative

abbrev image := OpenRestriction.image f i N
abbrev pulledCover := (RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V

variable
  [IsIso (RelativeCech.Refinement.homology ((Principal.AdditiveSections.opens U hU).obj (⊤_ _))
    B J s (Principal.NestedPushforward.original f i N c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (Principal.NestedPushforward.original f i N c)) (g+c))]

def sourceComparison :
    (AffinePrincipal.Injective.Comparison.source (OpenReindex.wideOpens (f ≫ i) U hU) W N c).homology (g+c) ⟶
      (Affine.OrderedInjective.Comparison.source N c (pulledCover f i V)).homology (g+c) :=
  Principal.PresheafCover.Comparison.comparison
    (Principal.CechPushforwardCoordinates.pulled (f ≫ i).base (Principal.AdditiveSections.opens U hU)) W
    ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
    (RelativeCech.Reindex.mapped (f ≫ i).base ((Principal.AdditiveSections.opens U hU).obj ∘ W) J r)
    (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (pulledCover f i V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
    (RelativeCech.ReindexGlobal.leftRefinement (f ≫ i).base ((Principal.AdditiveSections.opens U hU).obj (⊤_ _)) B T l)
    (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t) (Affine.OrderedInjective.Comparison.sourcePresheaf N c) (g+c)

abbrev globalCoordinates := Principal.MappedSingleCoordinates.globalCoordinates
  (Principal.NestedPushforward.sourceFunctor (Y := Y)) (AffinePrincipal.Injective.Comparison.sheaf N)
  c g (pulledCover f i V)

abbrev reindex := homologyMap (OrderedCech.Reindex.iso (RelativeCech.ReindexData.preimage (f ≫ i).base) V
  (Reference.SinglePresheafCoordinates.presheaf N)).hom g

abbrev ambientComparison := Principal.PresheafSingleCoordinates.coefficientComparison
  (Reference.SinglePresheafCoordinates.presheaf (image f i N)) c g
  (Principal.AdditiveSections.opens U hU) W B J r s V T l t

abbrev localCoordinates := (Principal.AdditiveSections.forgetScalars U).map
  (Principal.SingleModuleCoordinates.moduleCoordinates U hU (image f i N) c W g (g+c) rfl).hom ≫
    (Principal.SingleModuleCoordinates.coefficientIso U hU (image f i N) W g).hom

theorem additive_hom : (ReferenceCoordinates.Reference.additiveIso f i U hU N).hom =
    𝟙 ((Principal.AdditiveSections.additiveFunctor U hU).obj (image f i N)) := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem local_comparison :
    (SupportedCoordinates.wideIso f i U hU W N c (g+c)).hom ≫
      (Principal.MappedSingleCoordinates.localCoordinates
        (Principal.NestedPushforward.sourceFunctor (Y := Y))
        (AffinePrincipal.Injective.Comparison.sheaf N) c g (OpenReindex.wideOpens (f ≫ i) U hU) W).hom =
    localCoordinates f i U hU W N c g := by
  have h := ReferenceCoordinates.Reference.wide_coordinates f i U hU W N c g (g+c) rfl
  rw [additive_hom, CategoryTheory.Functor.map_id, homologyMap_id, Category.comp_id] at h
  simp only [ReferenceCoordinates.Reference.sourceCoordinates, eqToIso_refl, Iso.refl_trans] at h
  convert h using 1 <;> rfl

theorem coefficient_comparison :
    (SupportedCoordinates.wideIso f i U hU W N c (g+c)).hom ≫
      sourceComparison f i U hU W B J r s V T l t N c g ≫
      (globalCoordinates f i V N c g).hom =
    localCoordinates f i U hU W N c g ≫ ambientComparison f i U hU W B J r s V T l t N c g ≫
      reindex f i V N g := by
  have hs := Principal.MappedSingleCoordinates.comparison
    (Principal.NestedPushforward.sourceFunctor (Y := Y)) (AffinePrincipal.Injective.Comparison.sheaf N)
    c g (Principal.CechPushforwardCoordinates.pulled (f ≫ i).base (Principal.AdditiveSections.opens U hU)) W
    ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
    (RelativeCech.Reindex.mapped (f ≫ i).base ((Principal.AdditiveSections.opens U hU).obj ∘ W) J r)
    (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (pulledCover f i V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
    (RelativeCech.ReindexGlobal.leftRefinement (f ≫ i).base ((Principal.AdditiveSections.opens U hU).obj (⊤_ _)) B T l)
    (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t)
  have hp := Principal.NestedPushforward.comparison f i (Principal.AdditiveSections.opens U hU)
    W B J r s V T l t N c g
  exact paste _ _ _ _ _ _ _ _ hs (local_comparison f i U hU W N c g) hp

def outputCoordinates := reindex f i V N g ≫ (globalCoordinates f i V N c g).inv

theorem comparison :
    (localCoordinates f i U hU W N c g ≫ ambientComparison f i U hU W B J r s V T l t N c g) ≫
      outputCoordinates f i V N c g =
    (SupportedCoordinates.wideIso f i U hU W N c (g+c)).hom ≫
      sourceComparison f i U hU W B J r s V T l t N c g := by
  apply (cancel_mono (globalCoordinates f i V N c g).hom).mp
  simp only [outputCoordinates, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (coefficient_comparison f i U hU W B J r s V T l t N c g).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.PushforwardCoordinates
