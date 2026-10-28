import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AffineCommonCover

/-! # Canonical Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover

noncomputable section

/-! Canonical complementary and common affine covers for an actual
principal support diagram. The refinements retain the original diagram
and an arbitrary specified global affine cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} [X.IsSeparated] {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ X.Opens) {ι : Type u} [LinearOrder ι] (W : ι → C) (O : X.Opens)

abbrev complementary := ComplementaryAffineCover.opens O

def LocalIndex : Type u := ι × ComplementaryAffineCover.Index O
instance localIndexOrder : LinearOrder (LocalIndex (ι := ι) O) :=
  IsWellOrder.linearOrder WellOrderingRel

def localCover : LocalIndex (ι := ι) O → X.Opens :=
  Relative.AffineCommonCover.opens (F.obj ∘ W) (complementary O)
def localLeft : FormalCoproduct.mk (LocalIndex (ι := ι) O) (localCover F W O) ⟶
    FormalCoproduct.mk ι (F.obj ∘ W) :=
  Relative.AffineCommonCover.left (F.obj ∘ W) (complementary O)
def localRight : FormalCoproduct.mk (LocalIndex (ι := ι) O) (localCover F W O) ⟶
    FormalCoproduct.mk (ComplementaryAffineCover.Index O) (complementary O) :=
  Relative.AffineCommonCover.right (F.obj ∘ W) (complementary O)

variable {μ : Type u} [LinearOrder μ] (V : μ → X.Opens)

def GlobalIndex : Type u := WithBot (ComplementaryAffineCover.Index O) × μ
instance globalIndexOrder : LinearOrder (GlobalIndex (μ := μ) O) :=
  IsWellOrder.linearOrder WellOrderingRel

def globalCover : GlobalIndex (μ := μ) O → X.Opens :=
  Relative.AffineCommonCover.opens
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) (complementary O)) V

def globalLeft : FormalCoproduct.mk (GlobalIndex (μ := μ) O) (globalCover F O V) ⟶
    FormalCoproduct.mk (WithBot (ComplementaryAffineCover.Index O))
      (RelativeCech.Intersections.cover (F.obj (⊤_ C)) (complementary O)) :=
  Relative.AffineCommonCover.left
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) (complementary O)) V

def globalRight : FormalCoproduct.mk (GlobalIndex (μ := μ) O) (globalCover F O V) ⟶
    FormalCoproduct.mk μ V :=
  Relative.AffineCommonCover.right
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) (complementary O)) V

variable (hF : ∀ r, IsAffineOpen (F.obj r))
  (hpunct : ∀ j, F.obj (W j) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ j, F.obj (W j))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))

include hpunct hcover in
omit [X.IsSeparated] [LinearOrder ι] in
theorem parameter_cover : (⨆ j, F.obj (W j)) = F.obj (⊤_ C) ⊓ O := by
  apply le_antisymm _ hcover
  apply iSup_le
  intro j
  exact le_inf (leOfHom (F.map (terminal.from (W j)))) (hpunct j)

include hpunct hcover in
omit [X.IsSeparated] [LinearOrder ι] in
theorem parameter_intersection_cover :
    (⨆ j, F.obj (⊤_ C) ⊓ F.obj (W j)) = F.obj (⊤_ C) ⊓ O := by
  calc
    _ = ⨆ j, F.obj (W j) := iSup_congr (fun j =>
      inf_eq_right.mpr (leOfHom (F.map (terminal.from (W j)))))
    _ = _ := parameter_cover F W O hpunct hcover

include hpunct hcover in
omit [X.IsSeparated] [LinearOrder ι] in
theorem local_cover : (⨆ j, F.obj (⊤_ C) ⊓ localCover F W O j) = F.obj (⊤_ C) ⊓ O :=
  Relative.AffineCommonCover.covers (F.obj ∘ W) (complementary O)
    (F.obj (⊤_ C)) (F.obj (⊤_ C) ⊓ O)
    (parameter_intersection_cover F W O hpunct hcover)
    (ComplementaryAffineCover.intersection_covers O (F.obj (⊤_ C)))

include hF in
omit [HasFiniteProducts C] [LinearOrder ι] in
theorem local_affine (j : LocalIndex (ι := ι) O) : IsAffineOpen (localCover F W O j) :=
  Relative.AffineCommonCover.affine (F.obj ∘ W) (complementary O)
    (fun j => hF (W j)) (ComplementaryAffineCover.affine O) j

include hglobal in
omit [X.IsSeparated] in
theorem ambient_cover :
    (⨆ j, RelativeCech.Intersections.cover (F.obj (⊤_ C)) (complementary O) j) = ⊤ :=
  ComplementaryAffineCover.cover_top O (F.obj (⊤_ C)) hglobal

include hglobal hV in
omit [LinearOrder μ] in
omit [X.IsSeparated] in
theorem global_cover : iSup (globalCover F O V) = ⊤ := by
  have h := Relative.AffineCommonCover.covers
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) (complementary O)) V ⊤ ⊤
    (by simpa only [top_inf_eq] using ambient_cover F O hglobal)
    (by simpa only [top_inf_eq] using hV)
  simpa only [GlobalIndex, globalCover, top_inf_eq] using h

include hF haV in
omit [LinearOrder μ] in
theorem global_affine (j : GlobalIndex (μ := μ) O) : IsAffineOpen (globalCover F O V j) :=
  Relative.AffineCommonCover.affine
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) (complementary O)) V
    (ComplementaryAffineCover.cover_affine O (F.obj (⊤_ C)) (hF _)) haV j

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover
