import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionCechRefinement

/-! # Canonical Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalRefinement

noncomputable section

/-! Canonical complementary and common affine covers satisfy the actual
refinement-isomorphism hypotheses for the original single sheaf and its
chosen integer injective resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective.Comparison
variable {X : Scheme.{0}} [X.IsSeparated] {C : Type} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ X.Opens) {ι : Type} [LinearOrder ι] (W : ι → C) (O : X.Opens)
  (hF : ∀ r, IsAffineOpen (F.obj r))
  (hpunct : ∀ j, F.obj (W j) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ j, F.obj (W j))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)
  {μ : Type} [LinearOrder μ] (V : μ → X.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (N : X.Modules) [N.IsQuasicoherent] (c q : ℕ)

include hF hpunct hcover in
omit [LinearOrder ι] in
theorem relative_source :
    IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C))
      (CanonicalCover.complementary O) (CanonicalCover.localCover F W O) (CanonicalCover.localRight F W O) (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q) :=
  Affine.SingleCechRefinement.relative (F.obj (⊤_ C)) (hF _)
    (CanonicalCover.complementary O) (CanonicalCover.localCover F W O) (CanonicalCover.localRight F W O) (F.obj (⊤_ C) ⊓ O)
    (ComplementaryAffineCover.intersection_covers O (F.obj (⊤_ C)))
    (CanonicalCover.local_cover F W O hpunct hcover)
    (ComplementaryAffineCover.affine O) (CanonicalCover.local_affine F W O hF) N c q

include hF hglobal hV haV in
theorem ordered_source :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V (CanonicalCover.globalCover F O V)
      (CanonicalCover.globalRight F O V) (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q) :=
  Affine.SingleCechRefinement.ordered V (CanonicalCover.globalCover F O V) (CanonicalCover.globalRight F O V)
    haV (CanonicalCover.global_affine F O V hF haV) N c hV (CanonicalCover.global_cover F O V hglobal hV) q

include hF hpunct hcover in
omit [LinearOrder ι] in
theorem relative_integer :
    IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C))
      (CanonicalCover.complementary O) (CanonicalCover.localCover F W O) (CanonicalCover.localRight F W O) (Affine.OrderedInjective.Comparison.integerPresheaf N c) q) :=
  Affine.ResolutionCechRefinement.relative_integer (F.obj (⊤_ C)) (hF _)
    (CanonicalCover.complementary O) (CanonicalCover.localCover F W O) (CanonicalCover.localRight F W O) (F.obj (⊤_ C) ⊓ O)
    (ComplementaryAffineCover.intersection_covers O (F.obj (⊤_ C)))
    (CanonicalCover.local_cover F W O hpunct hcover)
    (ComplementaryAffineCover.affine O) (CanonicalCover.local_affine F W O hF) N c q

include hF hglobal hV haV in
theorem ordered_integer :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V (CanonicalCover.globalCover F O V)
      (CanonicalCover.globalRight F O V) (Affine.OrderedInjective.Comparison.integerPresheaf N c)) q) :=
  Affine.ResolutionCechRefinement.ordered_integer V (CanonicalCover.globalCover F O V) (CanonicalCover.globalRight F O V)
    haV (CanonicalCover.global_affine F O V hF haV) N c hV (CanonicalCover.global_cover F O V hglobal hV) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalRefinement
