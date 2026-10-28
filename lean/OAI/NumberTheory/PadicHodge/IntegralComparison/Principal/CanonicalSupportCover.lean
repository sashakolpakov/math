import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSupportCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleSupportedCover

/-! # Canonical Support Cover -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalSupportCover

/-! The selected-support comparison on canonical complementary and common
affine covers. Every refinement isomorphism is derived from the geometric
conditions and the actual chosen-resolution augmentation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalRefinement
variable {X : Scheme.{0}} [X.IsSeparated] {C : Type} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ X.Opens) {ι : Type} [LinearOrder ι] (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (O : X.Opens) (hF : ∀ r, IsAffineOpen (F.obj r))
  (hpunct : ∀ j, F.obj (W j) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ j, F.obj (W j))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)
  (N : X.Modules) [N.IsQuasicoherent] (c : ℕ)
  {μ : Type} [LinearOrder μ] (V : μ → X.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j)) (q : ℕ)

def comparison :
    (AffinePrincipal.Injective.Comparison.source F W N c).homology q ⟶
      (Affine.OrderedInjective.Comparison.source N c V).homology q := by
  letI := CanonicalRefinement.relative_source F W O hF hpunct hcover N c q
  letI := CanonicalRefinement.ordered_source F O hF hglobal V hV haV N c q
  exact SingleSupportedCover.originalComparison F W N c
    (CanonicalCover.complementary O) (CanonicalCover.localCover F W O) (CanonicalCover.localLeft F W O) (CanonicalCover.localRight F W O)
    V (CanonicalCover.globalCover F O V) (CanonicalCover.globalLeft F O V) (CanonicalCover.globalRight F O V) q

variable (G : C ⥤ X.Opens)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G]
  (P : X.Opens) (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions F G W O P)

include H hV haV in
theorem candidate_comparison :
    H.candidate N c q ≫
      comparison F W O H.wide_affine H.wide_punctured H.wide_cover H.wide_global N c V hV haV q =
    comparison G W P H.selected.wide_affine H.selected.wide_punctured
      H.selected.wide_cover H.selected.wide_global N c V hV haV q := by
  let := CanonicalRefinement.relative_source F W O H.wide_affine H.wide_punctured H.wide_cover N c q
  let := CanonicalRefinement.ordered_source F O H.wide_affine H.wide_global V hV haV N c q
  let := CanonicalRefinement.relative_integer F W O H.wide_affine H.wide_punctured H.wide_cover N c q
  let := CanonicalRefinement.ordered_integer F O H.wide_affine H.wide_global V hV haV N c q
  let := CanonicalRefinement.relative_source G W P H.selected.wide_affine H.selected.wide_punctured
    H.selected.wide_cover N c q
  let := CanonicalRefinement.ordered_source G P H.selected.wide_affine H.selected.wide_global V hV haV N c q
  let := CanonicalRefinement.relative_integer G W P H.selected.wide_affine H.selected.wide_punctured
    H.selected.wide_cover N c q
  let := CanonicalRefinement.ordered_integer G P H.selected.wide_affine H.selected.wide_global V hV haV N c q
  exact SelectedSupportCover.comparison F G W O P H N c
    (CanonicalCover.complementary O) (CanonicalCover.localCover F W O) (CanonicalCover.localLeft F W O) (CanonicalCover.localRight F W O)
    (CanonicalCover.complementary P) (CanonicalCover.localCover G W P) (CanonicalCover.localLeft G W P) (CanonicalCover.localRight G W P)
    V haV (CanonicalCover.globalCover F O V) (CanonicalCover.globalLeft F O V) (CanonicalCover.globalRight F O V)
    (CanonicalCover.globalCover G P V) (CanonicalCover.globalLeft G P V) (CanonicalCover.globalRight G P V)
    (ComplementaryAffineCover.le O) (ComplementaryAffineCover.le P) q

end NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalSupportCover

namespace NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalSupportCover.SingleIndependence

/-! The original single-sheaf comparison is independent of the auxiliary
complementary and common covers, with its specified global cover retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalRefinement
variable {X : Scheme.{0}} [X.IsSeparated] {C : Type} [Preorder C] [HasFiniteProducts C]
  (F G : C ⥤ X.Opens) {ι : Type} [LinearOrder ι] (W : ι → C)
  [∀ (d : ℕ) (a : Fin (d+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  [∀ (d : ℕ) (a : Fin (d+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G]
  (O P : X.Opens) (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions F G W O P)
  (N : X.Modules) [N.IsQuasicoherent] (c : ℕ)
  {μ : Type} [LinearOrder μ] (V : μ → X.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j)) (q : ℕ)

omit [∀ (d : ℕ) (a : Fin (d + 1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G] in
theorem canonical_comparison :
    CanonicalSupportCover.comparison F W O H.wide_affine H.wide_punctured
      H.wide_cover H.wide_global N c V hV haV q =
    H.forgetSupport N c q ≫ Affine.OrderedInjective.Comparison.coverOutput N c V haV q := by
  let := CanonicalRefinement.relative_source F W O H.wide_affine H.wide_punctured H.wide_cover N c q
  let := CanonicalRefinement.ordered_source F O H.wide_affine H.wide_global V hV haV N c q
  let := CanonicalRefinement.relative_integer F W O H.wide_affine H.wide_punctured H.wide_cover N c q
  let := CanonicalRefinement.ordered_integer F O H.wide_affine H.wide_global V hV haV N c q
  exact SingleSupportedCover.comparison F G W O P H N c
    (CanonicalCover.complementary O) (CanonicalCover.localCover F W O) (CanonicalCover.localLeft F W O) (CanonicalCover.localRight F W O)
    V haV (CanonicalCover.globalCover F O V) (CanonicalCover.globalLeft F O V) (CanonicalCover.globalRight F O V)
    (ComplementaryAffineCover.le O) q

variable {κ ν ρ : Type} [LinearOrder κ] [LinearOrder ν] [LinearOrder ρ]
  (B : κ → X.Opens) (J : ν → X.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (T : ρ → X.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (hB : ∀ j, B j ≤ O)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q)]
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (Affine.OrderedInjective.Comparison.integerPresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (Affine.OrderedInjective.Comparison.integerPresheaf N c)) q)]

include hB in
omit [∀ (d : ℕ) (a : Fin (d + 1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G] in
theorem comparison :
    SingleSupportedCover.originalComparison F W N c B J r s V T l t q =
    CanonicalSupportCover.comparison F W O H.wide_affine H.wide_punctured
      H.wide_cover H.wide_global N c V hV haV q :=
  (SingleSupportedCover.comparison F G W O P H N c B J r s V haV T l t hB q).trans
    (canonical_comparison F G W O P H N c V hV haV q).symm

end NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalSupportCover.SingleIndependence

end

end OAI
