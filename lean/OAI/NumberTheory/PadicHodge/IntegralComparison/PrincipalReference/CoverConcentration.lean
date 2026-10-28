import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.CommonConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverConcentration

/-! # Cover Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverConcentration.Reference

noncomputable section

/-! The actual principal-to-original-cover map retains the canonical
concentration on both sides of the local residue calculation. -/
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
  (J : ν → X.Opens) (hJ : ∀ i, IsAffineOpen (J i))
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside f.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)))
  (V : κ → X.Opens) (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients K) q)]
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients
      ((single X.Modules (.up ℕ) c).obj (K.homology c))) q)]
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover.outside f.ker
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover.opens O
local instance survivor_qc : (K.homology c).IsQuasicoherent :=
  QuasicoherentTruncation.cohomology K c
local instance single_qc (q : ℕ) :
    (((single X.Modules (.up ℕ) c).obj (K.homology c)).X q).IsQuasicoherent :=
  QuasicoherentTruncation.single (K.homology c) c q

include hJ in
theorem comparison :
    (Principal.AdditiveSections.forgetScalars U).map
      (Concentration.Reference.iso U hU W K c hK q).hom ≫
        CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV
          (K := (single X.Modules (.up ℕ) c).obj (K.homology c)) q =
    CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := K) q ≫
      (Additive.OrderedCechConcentration.iso V haV K c hK q).hom := by
  have hp := Principal.RelativeConcentration.concentration U hU W K c hK q
  have hr := Relative.CommonConcentration.comparison (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU)
    (Principal.RelativeConcentration.family U hU W) (Principal.RelativeConcentration.family_affine U hU W) C (ComplementaryAffineCover.affine O)
    J hJ r s K c hK q
  have hg := Additive.OrderedCoverConcentration.square
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
    K c hK q
  have hpr := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hp hr
  have h := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hpr hg
  simpa only [CoverTransfer.Reference.comparison,
    Principal.GlobalTransferRecovery.comparison, PointComplementGlobalCover.iso,
    Functor.mapIso_hom, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverConcentration.Reference
