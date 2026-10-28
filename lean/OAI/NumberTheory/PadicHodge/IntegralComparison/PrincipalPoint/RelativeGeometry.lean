import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointParameterCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PurePushforwardRefinement

/-! # Relative Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry

noncomputable section

/-! The original parameter family and an actual complementary affine
cover have a canonical common refinement. Its inverse on a pure
closed-pushforward complex follows from the genuine source cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Y T : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
  (i : X ⟶ Y) [IsClosedImmersion i] (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Y.Opens) (hU : IsAffineOpen U)
  {c g : ℕ} (s : Fin c → Γ(Y, U)) (t : Fin g → Γ(Y, U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U, hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U, hU⟩)

abbrev outside := SectionIdealPuncturedCover.outside (s₀ ≫ i).ker
abbrev parameters := Principal.RelativeConcentration.family U hU (Fraction.family U t)
abbrev complementary := ComplementaryAffineCover.opens (outside i s₀)
abbrev CommonIndex := ULift.{u} (Fin g) × ComplementaryAffineCover.Index (outside i s₀)
instance commonOrder : LinearOrder (CommonIndex (g := g) i s₀) :=
  IsWellOrder.linearOrder WellOrderingRel
abbrev common := Relative.AffineCommonCover.opens (parameters U hU t) (complementary i s₀)
abbrev left := Relative.AffineCommonCover.left (parameters U hU t) (complementary i s₀)
abbrev right := Relative.AffineCommonCover.right (parameters U hU t) (complementary i s₀)

omit [Y.IsSeparated] in
theorem ambient_eq : Principal.RelativeConcentration.ambient U hU = U := Principal.TerminalScalars.open_eq U hU
omit [Y.IsSeparated] in
theorem parameters_affine (j : ULift.{u} (Fin g)) : IsAffineOpen (parameters U hU t j) :=
  hU.basicOpen (t j.down)
omit [X.IsSeparated] [Y.IsSeparated] [IsClosedImmersion i] [IsClosedImmersion s₀] in
theorem complementary_affine (j : ComplementaryAffineCover.Index (outside i s₀)) :
    IsAffineOpen (complementary i s₀ j) := ComplementaryAffineCover.affine _ j
omit [X.IsSeparated] [IsClosedImmersion i] [IsClosedImmersion s₀] in
theorem common_affine (j : CommonIndex (g := g) i s₀) : IsAffineOpen (common i s₀ U hU t j) :=
  Relative.AffineCommonCover.affine _ _ (parameters_affine U hU t) (complementary_affine i s₀) j
omit [X.IsSeparated] [Y.IsSeparated] [IsClosedImmersion i] [IsClosedImmersion s₀] in
theorem complementary_outside (j : ComplementaryAffineCover.Index (outside i s₀)) :
    complementary i s₀ j ≤ outside i s₀ := ComplementaryAffineCover.le _ j
omit [X.IsSeparated] [Y.IsSeparated] [IsClosedImmersion i] [IsClosedImmersion s₀] in
theorem common_outside (j : CommonIndex (g := g) i s₀) : common i s₀ U hU t j ≤ outside i s₀ :=
  inf_le_right.trans (complementary_outside i s₀ j.2)

abbrev sourceOutside := i ⁻¹ᵁ U ⊓ SectionIdealPuncturedCover.outside s₀.ker

include hs hst in
omit [X.IsSeparated] in
omit [Y.IsSeparated] in
theorem parameter_cover : (⨆ j, i ⁻¹ᵁ (Principal.RelativeConcentration.ambient U hU ⊓ parameters U hU t j)) = sourceOutside i s₀ U := by
  rw [ambient_eq]
  change (⨆ j : ULift.{u} (Fin g), i ⁻¹ᵁ (U ⊓ Y.basicOpen (t j.down))) = _
  rw [iSup_ulift]
  exact Closed.PointParameterCover.principal_cover i s₀ U hU s t hs hst

omit [X.IsSeparated] in
omit [Y.IsSeparated] in
theorem complementary_cover :
    (⨆ j, i ⁻¹ᵁ (Principal.RelativeConcentration.ambient U hU ⊓ complementary i s₀ j)) = sourceOutside i s₀ U := by
  rw [ambient_eq]
  exact Closed.PointParameterCover.complementary_cover i s₀ U

include hs hst in
omit [X.IsSeparated] in
omit [Y.IsSeparated] in
theorem common_cover : (⨆ j, i ⁻¹ᵁ (Principal.RelativeConcentration.ambient U hU ⊓ common i s₀ U hU t j)) =
    sourceOutside i s₀ U := by
  apply le_antisymm
  · apply iSup_le
    intro j
    exact ((Opens.map i.base).monotone (inf_le_inf_left _ inf_le_left)).trans
      ((le_iSup (fun k => i ⁻¹ᵁ (Principal.RelativeConcentration.ambient U hU ⊓ parameters U hU t k)) j.1).trans
        (parameter_cover i s₀ U hU s t hs hst).le)
  · intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((parameter_cover i s₀ U hU s t hs hst).symm ▸ hx)
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp ((complementary_cover i s₀ U hU).symm ▸ hx)
    exact Opens.mem_iSup.mpr ⟨(j,k), hj.1, hj.2, hk.2⟩

variable (K : CochainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (d : ℕ) (hK : ∀ q, q ≠ d → K.ExactAt q)
  (M : X.Modules) [hM : M.IsQuasicoherent]
  (e : K.homology d ≅ (Scheme.Modules.pushforward i).obj M)

include hs hst hK M hM e in
theorem right_isIso (q : ℕ) : IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (complementary i s₀) (common i s₀ U hU t) (right i s₀ U hU t)
      (Relative.AdditiveCechConcentration.coefficients K) q) :=
  Relative.PurePushforwardRefinement.isIso i (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU)
    (complementary i s₀) (complementary_affine i s₀)
    (common i s₀ U hU t) (common_affine i s₀ U hU t) (right i s₀ U hU t)
    (sourceOutside i s₀ U) (complementary_cover i s₀ U hU)
    (common_cover i s₀ U hU s t hs hst)
    (fun j => ((Principal.RelativeConcentration.ambient_affine U hU).inf (complementary_affine i s₀ j)).preimage i)
    (fun j => ((Principal.RelativeConcentration.ambient_affine U hU).inf (common_affine i s₀ U hU t j)).preimage i)
    K d hK M e q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry
