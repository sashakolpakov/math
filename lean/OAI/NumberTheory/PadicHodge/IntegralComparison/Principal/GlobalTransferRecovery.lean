import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedTransferRecovery

/-! # Global Transfer Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.GlobalTransferRecovery

noncomputable section

/-! The actual principal localization and original resolution transfer
extend to the same global transferred point class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → SectionPresheaf.Index U)
  (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (J : ν → X.Opens) (hJ : ∀ i, IsAffineOpen (J i))
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (RelativeConcentration.family U hU V))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ W)
  {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (P.X q).IsQuasicoherent]
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)
  (c : ℕ) (hP : ∀ k, k ≠ c → P.ExactAt k)
  (f : Z ⟶ X) [IsClosedImmersion f] (N : Z.Modules)
  (e : P.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hVO : ∀ i, SectionPresheaf.openSubset U (V i) ≤ SectionIdealPuncturedCover.outside f.ker)
  (hWO : ∀ i, W i ≤ SectionIdealPuncturedCover.outside f.ker)
  (hJO : ∀ i, J i ≤ SectionIdealPuncturedCover.outside f.ker)
  (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (RelativeConcentration.ambient U hU) W J s
    (Relative.AdditiveCechConcentration.coefficients K) q)]

def comparison := (RelativeConcentration.comparison U hU V K q).hom ≫
  RelativeCech.CommonRefinement.comparison (RelativeConcentration.ambient U hU) (RelativeConcentration.family U hU V) W J r s
    (Relative.AdditiveCechConcentration.coefficients K) q

include hJ hVO hWO hJO in
theorem recovery :
    (PrincipalReference.SupportedClass.Reference.localize U hU V P c hP f N e hVO q ≫
      (AdditiveSections.forgetScalars U).map (RelativeTransfer.map U hU V q l a)) ≫
        comparison U hU V W J r s (K := K) q =
    (Relative.AdditiveCechGlobalConcentration.SupportedPureClass.globalEdge (RelativeConcentration.ambient U hU) W P c q ≫
      (Relative.AdditiveCechGlobalConcentration.SupportedPureClass.globalSurvivorIso (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
        W hW P c hP q).inv) ≫
          RelativeCech.RefinementTransfer.globalMap (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
            W hW q l a := by
  unfold comparison
  rw [← Category.assoc,
    RelativeTransfer.localized_map U hU V q l a c hP f N e hVO]
  exact Relative.SupportedTransferRecovery.recovery (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
    (RelativeConcentration.family U hU V) (RelativeConcentration.family_affine U hU V) W hW J hJ r s l a c hP f N e hVO hWO hJO q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.GlobalTransferRecovery
