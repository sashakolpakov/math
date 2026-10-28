import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.PushforwardCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Coefficient

/-! # Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Source.ReferenceComparison

noncomputable section

/-! The original principal comparison, with its genuine base-cohomology
output, agrees with the source single-sheaf comparison under the actual
ordered pushforward coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (x : D ⟶ E) (y : E ⟶ F) (u : B ⟶ E) (v : A ⟶ F)
    (ho : b ≫ x = u) (hs : (a ≫ u) ≫ y = v) : (a ≫ b) ≫ (x ≫ y) = v := by
  rw [Category.assoc, ← Category.assoc b x y, ho]
  simpa only [Category.assoc] using hs

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {Y X Z Q S : Scheme.{0}} [Z.IsSeparated]
  (f : Y ⟶ X) (i : X ⟶ Z) (π : Z ⟶ S)
  (U : Z.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (W : ι → Principal.SectionPresheaf.Index U) (a : Q ⟶ Z) [IsClosedImmersion a] (haU : ⊤ ≤ a ⁻¹ᵁ U)
  (J : ν → Z.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside a.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside a.ker)))
  (V : κ → Z.Opens) (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (N : Y.Modules) [(PrincipalSource.OpenRestriction.image f i N).IsQuasicoherent]
  (c g : ℕ)

abbrev image := PrincipalSource.OpenRestriction.image f i N
abbrev complement := ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside a.ker)
abbrev globalCover := PointComplementGlobalCover.common a (Principal.RelativeConcentration.ambient U hU) V
abbrev globalLeft := PointComplementGlobalCover.left a (Principal.RelativeConcentration.ambient U hU) V
abbrev globalRight := PointComplementGlobalCover.right a (Principal.RelativeConcentration.ambient U hU) V
abbrev original := Principal.NestedPushforward.original f i N c

local instance single_qc (k : ℕ) :
    (((single Z.Modules (.up ℕ) c).obj (image f i N)).X k).IsQuasicoherent :=
  QuasicoherentTruncation.single (image f i N) c k

variable [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU) (complement a) J s
  (original f i N c) (g+c))]

include haU hV haV in
private theorem global_isIso :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V (globalCover U hU a V)
      (globalRight U hU a V) (original f i N c)) (g+c)) :=
  Additive.OrderedCoverRefinement.homology_isIso V (globalCover U hU a V)
    (globalRight U hU a V) hV
    (PointComplementGlobalCover.common_covers a (Principal.RelativeConcentration.ambient U hU)
      (CoverTransfer.Reference.contains U hU a haU) V hV)
    haV (PointComplementGlobalCover.common_affine a (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU) V haV)
    ((single Z.Modules (.up ℕ) c).obj (image f i N)) (g+c)

def originalMap :=
  PrincipalSource.PushforwardCoordinates.localCoordinates f i U hU W N c g ≫
    SingleBaseCoordinates.Reference.coefficientComparison π U hU W a haU J r s V hV haV
      (image f i N) c g (g+c) rfl

def sourceOutput :=
  (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V (image f i N) g).hom ≫
    PrincipalSource.PushforwardCoordinates.outputCoordinates f i V N c g

def sourceComparison := by
  letI := global_isIso f i U hU a haU V hV haV N c g
  exact PrincipalSource.PushforwardCoordinates.sourceComparison f i U hU W (complement a) J r s
    V (globalCover U hU a V) (globalLeft U hU a V) (globalRight U hU a V) N c g

theorem comparison :
    originalMap f i π U hU W a haU J r s V hV haV N c g ≫ sourceOutput f i π V N c g =
    (PrincipalSource.SupportedCoordinates.wideIso f i U hU W N c (g+c)).hom ≫
      sourceComparison f i U hU W a haU J r s V hV haV N c g := by
  let := global_isIso f i U hU a haU V hV haV N c g
  have ho := Coefficient.Reference.comparison π U hU W a haU J r s V hV haV
    (image f i N) c g (g+c) rfl
  have hs := PrincipalSource.PushforwardCoordinates.comparison f i U hU W (complement a) J r s
    V (globalCover U hU a V) (globalLeft U hU a V) (globalRight U hU a V) N c g
  exact paste _ _ _ _ _ _ ho hs

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Source.ReferenceComparison
