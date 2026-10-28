import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueRelativeCechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal

/-! # Canonical Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CanonicalRefinement

noncomputable section

/-! The actual native crystalline resolution satisfies the relative and
ordered refinement hypotheses for the canonical support covers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  {C : Type} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ X.left.Opens) {ι : Type} [LinearOrder ι] (W : ι → C) (O : X.left.Opens)
  (hpunct : ∀ j, F.obj (W j) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ j, F.obj (W j))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)
  {μ : Type} [LinearOrder μ] (V : μ → X.left.Opens) (hV : iSup V = ⊤)

include hpunct hcover in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [LinearOrder ι] in
theorem relative (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover F W O) (Principal.CanonicalCover.localRight F W O)
      (CechIso.ResolutionGlobal.presheaf p k n X Y f I) q) := by
  exact FlasqueRelativeCechRefinement.relative.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) X.left
    (ModelSheafComparison.target p k n X Y f I)
    (AdditiveGlobal.ResolutionFlasque.term_flasque p k n X Y f I)
    (F.obj (⊤_ C)) (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover F W O) (Principal.CanonicalCover.localRight F W O) O
    (fun j => inf_le_right.trans (ComplementaryAffineCover.le O j))
    (fun j => inf_le_right.trans ((leOfHom ((Principal.CanonicalCover.localRight F W O).φ j)).trans
      (ComplementaryAffineCover.le O _)))
    (ComplementaryAffineCover.intersection_covers O (F.obj (⊤_ C))).ge
    (Principal.CanonicalCover.local_cover F W O hpunct hcover).ge q

include hglobal hV in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem ordered (q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V (Principal.CanonicalCover.globalCover F O V)
      (Principal.CanonicalCover.globalRight F O V) (CechIso.ResolutionGlobal.presheaf p k n X Y f I)) q) :=
  FlasqueRelativeCechRefinement.ordered.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) X.left
    (ModelSheafComparison.target p k n X Y f I)
    (AdditiveGlobal.ResolutionFlasque.term_flasque p k n X Y f I)
    V (Principal.CanonicalCover.globalCover F O V) (Principal.CanonicalCover.globalRight F O V) hV (Principal.CanonicalCover.global_cover F O V hglobal hV) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CanonicalRefinement
