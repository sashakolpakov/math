import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.GlobalTransferRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.PointComplementGlobalCover

/-! # Cover Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverTransfer.Reference

noncomputable section

/-! The actual principal supported class and original resolution
transfer land in the same class on an arbitrary original affine cover. -/
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

include hfU in
omit [X.IsSeparated] [IsClosedImmersion f] in
theorem contains : ⊤ ≤ f ⁻¹ᵁ Principal.RelativeConcentration.ambient U hU := by
  change ⊤ ≤ f ⁻¹ᵁ Principal.SectionPresheaf.openSubset U (⊤_ Principal.SectionPresheaf.Index U)
  rw [Principal.TerminalScalars.open_eq U hU]
  exact hfU

variable {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (P.X q).IsQuasicoherent] [∀ q, (K.X q).IsQuasicoherent]
  [∀ q, (T.X q).IsQuasicoherent] (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)
  (c : ℕ) (hP : ∀ k, k ≠ c → P.ExactAt k) (N : Z.Modules)
  (e : P.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hWO : ∀ i, Principal.SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)
  (hJO : ∀ i, J i ≤ SectionIdealPuncturedCover.outside f.ker)
  (q : ℕ) [hiso : IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients K) q)]

local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover.outside f.ker
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover.opens O

def comparison := by
  letI := hiso
  exact Principal.GlobalTransferRecovery.comparison U hU W C J r s (K := K) q ≫
    (PointComplementGlobalCover.iso f (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU)
      (contains U hU f hfU) V hV haV K q).hom

include hJ hWO hJO in
theorem recovery :
    (SupportedClass.Reference.localize U hU W P c hP f N e hWO q ≫
      (Principal.AdditiveSections.forgetScalars U).map
        (Principal.RelativeTransfer.map U hU W q l a)) ≫
      comparison U hU W f hfU J r s V hV haV q =
    Global.PureSectionClass.map V haV P c hP q ≫
      IntrinsicOrdered.CechTransferCoordinates.Intrinsic.genericMap (𝟙 X) V haV q l a := by
  unfold comparison
  rw [← Category.assoc,
    Principal.GlobalTransferRecovery.recovery U hU W C
      (ComplementaryAffineCover.affine O) J hJ r s l a c hP f N e hWO
      (ComplementaryAffineCover.le O) hJO q]
  exact PointComplementGlobalCover.pure_transfer f (Principal.RelativeConcentration.ambient U hU) (Principal.RelativeConcentration.ambient_affine U hU)
    (contains U hU f hfU) V hV haV K c hP l a q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverTransfer.Reference
