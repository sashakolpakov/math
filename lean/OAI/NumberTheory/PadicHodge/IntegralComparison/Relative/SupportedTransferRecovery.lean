import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.ForwardRefinementClass

/-! # Supported Transfer Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedTransferRecovery

noncomputable section

/-! A supported class passes through the original right/inverse-left
resolution comparison and recovers its global image. Only the target
refinement is inverted. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementTransfer
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (J : ν → X.Opens) (hJ : ∀ i, IsAffineOpen (J i))
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι V)
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ W)
  {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (P.X q).IsQuasicoherent]
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)
  (c : ℕ) (hP : ∀ k, k ≠ c → P.ExactAt k)
  (f : Z ⟶ X) [IsClosedImmersion f] (N : Z.Modules)
  (e : P.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hVO : ∀ i, V i ≤ SectionIdealPuncturedCover.outside f.ker)
  (hWO : ∀ i, W i ≤ SectionIdealPuncturedCover.outside f.ker)
  (hJO : ∀ i, J i ≤ SectionIdealPuncturedCover.outside f.ker)
  (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology U W J s (AdditiveCechConcentration.coefficients K) q)]

include hJ hVO hWO hJO in
theorem comparison :
    (SupportedPureClass.lift U hU V hV P c hP f N e hVO q ≫
      RelativeCech.RefinementTransfer.map U hU V hV q l a) ≫
        RelativeCech.CommonRefinement.comparison U V W J r s (AdditiveCechConcentration.coefficients K) q =
    (SupportedPureClass.lift U hU W hW P c hP f N e hWO q ≫
      RelativeCech.RefinementTransfer.map U hU W hW q l a) ≫ (RelativeCech.RefinementTransfer.extension U W q).app K := by
  apply ForwardRefinementClass.comparison
    (SupportedPureClass.lift U hU V hV P c hP f N e hVO q)
    (SupportedPureClass.lift U hU W hW P c hP f N e hWO q)
    _ _ _ _ (RelativeCech.RefinementTransfer.map U hU J hJ q l a) _ _ _
  · exact (SupportedPureClass.refinement U hU V hV P c hP
      f N e hVO J hJ r hJO q).trans
        (SupportedPureClass.refinement U hU W hW P c hP
          f N e hWO J hJ s hJO q).symm
  · exact RelativeCech.RefinementTransfer.refinement_square U hU V hV J hJ r q l a
  · exact RelativeCech.RefinementTransfer.refinement_square U hU W hW J hJ s q l a

include hJ hVO hWO hJO in
theorem recovery :
    (SupportedPureClass.lift U hU V hV P c hP f N e hVO q ≫
      RelativeCech.RefinementTransfer.map U hU V hV q l a) ≫
        RelativeCech.CommonRefinement.comparison U V W J r s (AdditiveCechConcentration.coefficients K) q =
    (AdditiveCechGlobalConcentration.SupportedPureClass.globalEdge U W P c q ≫
      (AdditiveCechGlobalConcentration.SupportedPureClass.globalSurvivorIso U hU W hW P c hP q).inv) ≫
        RelativeCech.RefinementTransfer.globalMap U hU W hW q l a := by
  rw [comparison U hU V hV W hW J hJ r s l a c hP f N e hVO hWO hJO q]
  rw [Category.assoc, RelativeCech.RefinementTransfer.extension_square, ← Category.assoc]
  exact congrArg (· ≫ RelativeCech.RefinementTransfer.globalMap U hU W hW q l a)
    (AdditiveCechGlobalConcentration.SupportedPureClass.recovery U hU W hW P c hP f N e hWO q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedTransferRecovery
