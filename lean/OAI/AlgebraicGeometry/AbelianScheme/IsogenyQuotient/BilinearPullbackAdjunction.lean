import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

/-! # Bilinear Pullback Adjunction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearPullbackAdjunction.Construction

noncomputable section

/-! The actual tensor pullback comparison gives the bilinear
adjunction and its faithfulness for line-sheaf inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
  (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)

include hM hN in
theorem bilinearAdjoint_injective {P : X.Modules} :
    Function.Injective (fun b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P => Picard.PoincareBundle.Tensor.PullbackMap.bilinearAdjoint f M N b) := by
  have : IsIso (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N) := Picard.PoincareBundle.Tensor.LinePullback.pullbackMap_isIso f M N hM hN
  intro b c h
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b = Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c
  apply (cancel_epi (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N)).mp
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap_postcomp, Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap_postcomp]
  simpa only [Picard.PoincareBundle.Bilinear.BilinearPullback.toHom, Equiv.apply_symm_apply] using h

theorem bilinearAdjoint_pullback {P : Y.Modules} (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    Picard.PoincareBundle.Tensor.PullbackMap.bilinearAdjoint f M N (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hN b) =
      b.postcomp ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P) := by
  have h := Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap_postcomp f M N (Picard.PoincareBundle.Bilinear.BilinearPullback.pulledHom f hM hN b)
  have hf : Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N ≫ Picard.PoincareBundle.Bilinear.BilinearPullback.pulledHom f hM hN b = (Scheme.Modules.pullback f).map (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) :=
    Picard.PoincareBundle.Bilinear.BilinearPullback.pulledHom_fac f hM hN b
  rw [hf] at h
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullback f).map (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)) =
        Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P := by
    rw [Adjunction.homEquiv_unit]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)).symm
  rw [hu, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp] at h
  simpa only [Picard.PoincareBundle.Bilinear.BilinearPullback.toHom, Equiv.apply_symm_apply, Picard.PoincareBundle.Bilinear.BilinearPullback.pullback] using h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearPullbackAdjunction.Construction
