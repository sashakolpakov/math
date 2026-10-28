import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexCoefficientIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ReindexIsomorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.NestedSinglePushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective

/-! # Nested Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.NestedPushforward

noncomputable section

/-! The original nested module pushforward comparison equals the
source single-sheaf comparison in literal ordered coefficient coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z)
  {C : Type} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Z.Opens)
  {ι κ ν μ ρ : Type}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Z.Opens) (J : ν → Z.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Z.Opens) (T : ρ → Z.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (N : Y.Modules) (c g : ℕ)
attribute [local instance] RelativeCech.ReindexData.preimage_limits
  CechPushforwardCoordinates.pulled_products

abbrev image := PrincipalSource.OpenRestriction.image f i N
abbrev coefficient := Reference.SinglePresheafCoordinates.presheaf N
abbrev original := Relative.AdditiveCechConcentration.coefficients
  ((single Z.Modules (.up ℕ) c).obj (image f i N))
abbrev plain := (single (Y.Opensᵒᵖ ⥤ AddCommGrpCat) (.up ℕ) c).obj (coefficient N)
abbrev ambientPlain := (single (Z.Opensᵒᵖ ⥤ AddCommGrpCat) (.up ℕ) c).obj
  (Reference.SinglePresheafCoordinates.presheaf (image f i N))
abbrev sourceFunctor := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat

variable
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s (original f i N c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (original f i N c)) (g+c))]

local instance ambient_plain_relative :
    IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s (ambientPlain f i N c) (g+c)) :=
  Cech.ComplexCoefficientIso.relative (Reference.SinglePresheafCoordinates.iso (image f i N) c)
    (F.obj (⊤_ C)) B J s (g+c)

local instance ambient_plain_ordered :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (ambientPlain f i N c)) (g+c)) :=
  Cech.ComplexCoefficientIso.ordered (Reference.SinglePresheafCoordinates.iso (image f i N) c)
    V T t (g+c)

local instance pushed_relative :
    IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
      (RelativeCech.ReindexTotal.pushed (f ≫ i).base (plain N c)) (g+c)) :=
  Cech.ComplexCoefficientIso.relative (NestedSinglePushforward.plainIso f i N c)
    (F.obj (⊤_ C)) B J s (g+c)

local instance pushed_ordered :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
      (RelativeCech.ReindexTotal.pushed (f ≫ i).base (plain N c))) (g+c)) :=
  Cech.ComplexCoefficientIso.ordered (NestedSinglePushforward.plainIso f i N c) V T t (g+c)

local instance source_plain_relative :
    IsIso (RelativeCech.Refinement.homology
      ((CechPushforwardCoordinates.pulled (f ≫ i).base F).obj (⊤_ C))
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
      (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (plain N c) (g+c)) :=
  Cech.ReindexIsomorphism.relative_source (f ≫ i).base (F.obj (⊤_ C)) B J s (plain N c) (g+c)

local instance source_plain_ordered :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
      (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t) (plain N c)) (g+c)) :=
  Cech.ReindexIsomorphism.ordered_source (f ≫ i).base V T t (plain N c) (g+c)

local instance source_sheaf_relative :
    IsIso (RelativeCech.Refinement.homology
      ((CechPushforwardCoordinates.pulled (f ≫ i).base F).obj (⊤_ C))
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
      (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (Affine.OrderedInjective.Comparison.sourcePresheaf N c) (g+c)) :=
  Cech.ComplexCoefficientIso.relative (Reference.SinglePresheafCoordinates.lastIso N c).symm
    ((CechPushforwardCoordinates.pulled (f ≫ i).base F).obj (⊤_ C))
    ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
    (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (g+c)

local instance source_sheaf_ordered :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
      (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t)
      (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) (g+c)) :=
  Cech.ComplexCoefficientIso.ordered (Reference.SinglePresheafCoordinates.lastIso N c).symm
    ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
    (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t) (g+c)

local instance source_mapped_relative :
    IsIso (RelativeCech.Refinement.homology
      ((CechPushforwardCoordinates.pulled (f ≫ i).base F).obj (⊤_ C))
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
      (RelativeCech.Reindex.mapped (f ≫ i).base B J s)
      (MappedSingleCoordinates.source (sourceFunctor (Y := Y))
        (AffinePrincipal.Injective.Comparison.sheaf N) c) (g+c)) :=
  (inferInstance : IsIso (RelativeCech.Refinement.homology
      ((CechPushforwardCoordinates.pulled (f ≫ i).base F).obj (⊤_ C))
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
      (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (Affine.OrderedInjective.Comparison.sourcePresheaf N c) (g+c)))

local instance source_mapped_ordered :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
      (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t)
      (MappedSingleCoordinates.source (sourceFunctor (Y := Y))
        (AffinePrincipal.Injective.Comparison.sheaf N) c)) (g+c)) :=
  (inferInstance : IsIso (homologyMap (OrderedCech.Refinement.totalMap
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
      (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t)
      (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) (g+c)))

local instance source_plain_raw_relative :
    IsIso (RelativeCech.Refinement.homology ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj (F.obj (⊤_ C)))
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
      (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (CechPushforwardSingle.singleComplex (coefficient N) c) (g+c)) :=
  (inferInstance : IsIso (RelativeCech.Refinement.homology
      ((CechPushforwardCoordinates.pulled (f ≫ i).base F).obj (⊤_ C))
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
      (RelativeCech.Reindex.mapped (f ≫ i).base B J s) (plain N c) (g+c)))

theorem comparison :
    PresheafSingleCoordinates.coefficientComparison
      (Reference.SinglePresheafCoordinates.presheaf (image f i N)) c g F W B J r s V T l t ≫
      homologyMap (OrderedCech.Reindex.iso (RelativeCech.ReindexData.preimage (f ≫ i).base) V (coefficient N)).hom g =
    MappedSingleCoordinates.coefficientComparison (sourceFunctor (Y := Y))
      (AffinePrincipal.Injective.Comparison.sheaf N) c g
      (CechPushforwardCoordinates.pulled (f ≫ i).base F) W
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ B) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ J)
      (RelativeCech.Reindex.mapped (f ≫ i).base (F.obj ∘ W) J r) (RelativeCech.Reindex.mapped (f ≫ i).base B J s)
      ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V) ((RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ T)
      (RelativeCech.ReindexGlobal.leftRefinement (f ≫ i).base (F.obj (⊤_ C)) B T l) (RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V T t) :=
  CechPushforwardSingle.comparison (f ≫ i).base F W B J r s V T l t (coefficient N) c g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.NestedPushforward
