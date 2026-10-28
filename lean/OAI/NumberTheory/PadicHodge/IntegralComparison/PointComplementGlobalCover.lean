import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AffineCommonCover

/-! # Point Complement Global Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PointComplementGlobalCover

noncomputable section

/-! The distinguished neighborhood together with the genuine affine
cover of the point complement compares to any original affine cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Z : Scheme.{u}} [X.IsSeparated]
  (f : Z ⟶ X) [IsClosedImmersion f]
  (U : X.Opens) (hU : IsAffineOpen U) (hfU : ⊤ ≤ f ⁻¹ᵁ U)
  {ι : Type u} [LinearOrder ι] (V : ι → X.Opens)
  (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))

abbrev outside := SectionIdealPuncturedCover.outside f.ker
abbrev cover := ComplementaryAffineCover.cover (outside f) U
abbrev CommonIndex := WithBot (ComplementaryAffineCover.Index (outside f)) × ι
instance commonOrder : LinearOrder (CommonIndex (ι := ι) f) :=
  IsWellOrder.linearOrder WellOrderingRel
abbrev common := Relative.AffineCommonCover.opens (cover f U) V
abbrev left := Relative.AffineCommonCover.left (cover f U) V
abbrev right := Relative.AffineCommonCover.right (cover f U) V

include hfU in
omit [X.IsSeparated] in
theorem covers : iSup (cover f U) = ⊤ :=
  ComplementaryAffineCover.cover_top (outside f) U
    (SectionIdealPuncturedCover.section_global U f hfU)

include hU in
omit [X.IsSeparated] [IsClosedImmersion f] in
theorem affine (j : WithBot (ComplementaryAffineCover.Index (outside f))) :
    IsAffineOpen (cover f U j) := ComplementaryAffineCover.cover_affine _ U hU j

include hfU hV in
omit [LinearOrder ι] in
omit [X.IsSeparated] in
theorem common_covers : iSup (common f U V) = ⊤ := by
  have h := Relative.AffineCommonCover.covers (cover f U) V ⊤ ⊤
    (by simpa only [top_inf_eq] using covers f U hfU)
    (by simpa only [top_inf_eq] using hV)
  simpa only [top_inf_eq] using h

include hU haV in
omit [LinearOrder ι] in
omit [IsClosedImmersion f] in
theorem common_affine (j : CommonIndex (ι := ι) f) : IsAffineOpen (common f U V j) :=
  Relative.AffineCommonCover.affine _ _ (affine f U hU) haV j

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

def iso (q : ℕ) := Additive.OrderedCover.Comparison.iso (cover f U) V (common f U V)
  (left f U V) (right f U V) (covers f U hfU) hV (common_covers f U hfU V hV)
  (affine f U hU) haV (common_affine f U hU V haV) K q

variable (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

abbrev pure_comparison (q : ℕ) := Global.PureCover.Comparison.comparison
  (cover f U) V (common f U V) (left f U V) (right f U V)
  (covers f U hfU) hV (common_covers f U hfU V hV)
  (affine f U hU) haV (common_affine f U hU V haV) K c hK q

variable {P T : CochainComplex X.Modules ℕ}
  [∀ q, (P.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (hP : ∀ q, q ≠ c → P.ExactAt q) (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)

abbrev pure_transfer (q : ℕ) := Global.PureCover.Comparison.transfer
  (cover f U) V (common f U V) (left f U V) (right f U V)
  (covers f U hfU) hV (common_covers f U hfU V hV)
  (affine f U hU) haV (common_affine f U hU V haV) P c hP q l a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PointComplementGlobalCover
