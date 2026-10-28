import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComparison

/-! # Pullback Section Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackSectionPairing

noncomputable section

/-! The arbitrary-pullback tensor comparison sends the actual pullback of a paired section to the pairing of the two pulled-back sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}}

theorem tensorPullbackComparison_pairing (f : X ⟶ Y) (M N : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (PullbackComparison.tensorPullbackComparison f M N).app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ProductSheaf.tensorModule M N)).app U
        ((Bifunctor.tensorBilinear M N).app U m n)) =
      (Bifunctor.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).app
        (f ⁻¹ᵁ U) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U n) := by
  have h := PullbackComparison.tensorPullbackComparison_spec f M N
  rw [← Bifunctor.tensorBilinear_postcomp, (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit] at h
  exact congrArg
    (fun β : Bilinear.Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj
      (ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))) =>
        β.app U m n) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackSectionPairing
