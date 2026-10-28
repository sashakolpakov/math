import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SingleBaseCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexCoefficientIso

/-! # Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Coefficient.Reference

noncomputable section

/-! The original principal single-class output has exactly the
unshifted presheaf comparison in its actual base-cohomology coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (W : ι → Principal.SectionPresheaf.Index U) (f : Z ⟶ X) [IsClosedImmersion f] (hfU : ⊤ ≤ f ⁻¹ᵁ U)
  (J : ν → X.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside f.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)))
  (V : κ → X.Opens) (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (N : X.Modules) [N.IsQuasicoherent] (c g q : ℕ) (hq : q=g+c)

abbrev original := Relative.AdditiveCechConcentration.coefficients
  (Reference.SinglePresheafCoordinates.moduleSingle N c)
abbrev plain := (single (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).obj
  (Reference.SinglePresheafCoordinates.presheaf N)
abbrev complement := ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)
abbrev common := PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V
abbrev left := PointComplementGlobalCover.left f (Principal.RelativeConcentration.ambient U hU) V
abbrev right := PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V

local instance single_qc (k : ℕ) :
    ((Reference.SinglePresheafCoordinates.moduleSingle N c).X k).IsQuasicoherent :=
  QuasicoherentTruncation.single N c k

variable [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU) (complement f) J s
  (original N c) q)]

include hfU hV haV in
private theorem original_global :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V (common U hU f V)
      (right U hU f V) (original N c)) q) :=
  Additive.OrderedCoverRefinement.homology_isIso V (common U hU f V) (right U hU f V) hV
    (PointComplementGlobalCover.common_covers f (Principal.RelativeConcentration.ambient U hU)
      (CoverTransfer.Reference.contains U hU f hfU) V hV)
    haV (PointComplementGlobalCover.common_affine f (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU) V haV)
    (Reference.SinglePresheafCoordinates.moduleSingle N c) q

local instance plain_relative :
    IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU) (complement f) J s (plain N c) q) :=
  Cech.ComplexCoefficientIso.relative (Reference.SinglePresheafCoordinates.iso N c)
    (Principal.RelativeConcentration.ambient U hU) (complement f) J s q

def coefficientComparison :
    (AugmentedOrdered.Cech.complex W
      ((Principal.AdditiveSections.opens U hU).op ⋙ Reference.SinglePresheafCoordinates.presheaf N)).homology g ⟶
    (OrderedCech.Projection.complex V (Reference.SinglePresheafCoordinates.presheaf N)).homology g := by
  letI := original_global U hU f hfU V hV haV N c q
  letI := Cech.ComplexCoefficientIso.ordered (Reference.SinglePresheafCoordinates.iso N c)
    V (common U hU f V) (right U hU f V) q
  exact Principal.PresheafSingleIndexedCoordinates.coefficientComparison
    (Reference.SinglePresheafCoordinates.presheaf N) c g (Principal.AdditiveSections.opens U hU)
    W (complement f) J r s V (common U hU f V) (left U hU f V) (right U hU f V) q hq

theorem comparison :
    SingleBaseCoordinates.Reference.coefficientComparison π U hU W f hfU J r s V hV haV N c g q hq ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V N g).hom =
    coefficientComparison U hU W f hfU J r s V hV haV N c g q hq := by
  simp only [coefficientComparison, SingleBaseCoordinates.Reference.coefficientComparison,
    SingleCoordinates.Reference.coefficientComparison,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Coefficient.Reference
