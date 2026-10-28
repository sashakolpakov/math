import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverTransfer

/-! # Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Presheaf.ReferenceComparison

noncomputable section

/-! The generic presheaf comparison is literally the original
principal-to-global comparison. Hence the original map commutes with
genuine native sheaf-complex maps, including the de Rham comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z : Scheme.{u}} [X.IsSeparated]
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (W : ι → Principal.SectionPresheaf.Index U) (f : Z ⟶ X) [IsClosedImmersion f]
  (hfU : ⊤ ≤ f ⁻¹ᵁ U)
  (J : ν → X.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside f.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)))
  (V : κ → X.Opens) (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients K) q)]

def presheafComparison := by
  letI := Additive.OrderedCoverRefinement.homology_isIso
    V (PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V) hV
    (PointComplementGlobalCover.common_covers f (Principal.RelativeConcentration.ambient U hU)
      (CoverTransfer.Reference.contains U hU f hfU) V hV)
    haV (PointComplementGlobalCover.common_affine f (Principal.RelativeConcentration.ambient U hU)
      (Principal.RelativeConcentration.ambient_affine U hU) V haV) K q
  exact Principal.PresheafCover.Comparison.comparison (Principal.AdditiveSections.opens U hU) W
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J r s
    V (PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.left f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V)
    (Relative.AdditiveCechConcentration.coefficients K) q

theorem original :
    (Principal.AdditiveSections.homologyIso U hU K W q).hom ≫
        presheafComparison U hU W f hfU J r s V hV haV K q =
      CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := K) q := by
  dsimp only [presheafComparison, Principal.PresheafCover.Comparison.comparison,
    CoverTransfer.Reference.comparison, Principal.GlobalTransferRecovery.comparison,
    Principal.RelativeConcentration.comparison, Relative.PresheafCommonRefinement.comparison,
    RelativeCech.CommonRefinement.comparison, PointComplementGlobalCover.iso,
    Additive.OrderedCover.Comparison.iso, Presheaf.OrderedCover.Comparison.comparison,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc]
  rfl

variable (L : CochainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ)
  (a : Relative.AdditiveCechConcentration.coefficients K ⟶ L)
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s L q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V
    (PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V) L) q)]

theorem naturality :
    (Principal.AdditiveSections.homologyIso U hU K W q).hom ≫
        homologyMap (Principal.PresheafCover.Comparison.totalMap
          (Principal.AdditiveSections.opens U hU) W a) q ≫
        Principal.PresheafCover.Comparison.comparison (Principal.AdditiveSections.opens U hU) W
          (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J r s
          V (PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V)
          (PointComplementGlobalCover.left f (Principal.RelativeConcentration.ambient U hU) V)
          (PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V) L q =
      CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := K) q ≫
        homologyMap ((Presheaf.OrderedCover.Comparison.totalFunctor V).map a) q := by
  let := Additive.OrderedCoverRefinement.homology_isIso
    V (PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V) hV
    (PointComplementGlobalCover.common_covers f (Principal.RelativeConcentration.ambient U hU)
      (CoverTransfer.Reference.contains U hU f hfU) V hV)
    haV (PointComplementGlobalCover.common_affine f (Principal.RelativeConcentration.ambient U hU)
      (Principal.RelativeConcentration.ambient_affine U hU) V haV) K q
  rw [Principal.PresheafCover.Comparison.naturality]
  rw [← Category.assoc]
  change ((Principal.AdditiveSections.homologyIso U hU K W q).hom ≫
      presheafComparison U hU W f hfU J r s V hV haV K q) ≫ _ = _
  rw [original]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Presheaf.ReferenceComparison
