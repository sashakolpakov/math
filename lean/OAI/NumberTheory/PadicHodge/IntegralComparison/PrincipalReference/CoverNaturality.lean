import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinementNaturality

/-! # Cover Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverNaturality.Reference

noncomputable section

/-! The original principal-to-global comparison commutes with genuine
coefficient morphisms, including the single-sheaf adjunction map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (W : ι → Principal.SectionPresheaf.Index U) (f : Z ⟶ X) [IsClosedImmersion f]
  (hfU : ⊤ ≤ f ⁻¹ᵁ U)
  (J : ν → X.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside f.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)))
  (V : κ → X.Opens) (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
  {K L : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
  (a : K ⟶ L) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients K) q)]
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients L) q)]
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover.outside f.ker
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover.opens O

theorem comparison :
    (Principal.AdditiveSections.forgetScalars U).map
      ((Concentration.Reference.functor U hU W q).map a) ≫
        CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := L) q =
    CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := K) q ≫
      (Additive.OrderedCechConcentration.functor V q).map a := by
  have hp := Principal.RelativeConcentration.naturality U hU W a q
  have hr := RelativeCech.CommonRefinementNaturality.naturality (Principal.RelativeConcentration.ambient U hU)
    (Principal.RelativeConcentration.family U hU W) C J r s (Relative.AdditiveCechConcentration.coefficientMap a) q
  have hg := Additive.OrderedCover.Comparison.naturality
    (PointComplementGlobalCover.cover f (Principal.RelativeConcentration.ambient U hU)) V
    (PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.left f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V)
    (PointComplementGlobalCover.covers f (Principal.RelativeConcentration.ambient U hU)
      (CoverTransfer.Reference.contains U hU f hfU)) hV
    (PointComplementGlobalCover.common_covers f (Principal.RelativeConcentration.ambient U hU)
      (CoverTransfer.Reference.contains U hU f hfU) V hV)
    (PointComplementGlobalCover.affine f (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU)) haV
    (PointComplementGlobalCover.common_affine f (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU) V haV)
    a q
  have hpr := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hp hr
  have h := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hpr hg
  simpa only [CoverTransfer.Reference.comparison,
    Principal.GlobalTransferRecovery.comparison, PointComplementGlobalCover.iso,
    Functor.comp_map, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverNaturality.Reference
