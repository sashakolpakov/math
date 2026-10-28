import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComparison

/-! # Pullback Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Invertibility of the canonical tensor comparison on open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def Bilinear.Sheaves.SheafBilinearMap.sourceIso {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N')
    (P : X.Modules) : Bilinear.Sheaves.SheafBilinearMap M N P ≃ Bilinear.Sheaves.SheafBilinearMap M' N' P where
  toFun β := β.precomp e.inv f.inv
  invFun β := β.precomp e.hom f.hom
  left_inv β := (β.precomp_comp e.inv f.inv e.hom f.hom).trans
    ((congrArg₂ (fun a b => β.precomp a b) e.hom_inv_id f.hom_inv_id).trans β.precomp_id)
  right_inv β := (β.precomp_comp e.hom f.hom e.inv f.inv).trans
    ((congrArg₂ (fun a b => β.precomp a b) e.inv_hom_id f.inv_hom_id).trans β.precomp_id)

def Tensor.PullbackOpen.bilinearOpenPullbackEquiv (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    (P : X.Modules) :
    Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P ≃
      Bilinear.Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P) :=
  (Bilinear.Sheaves.SheafBilinearMap.sourceIso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N).symm P).trans
    (Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N P)

theorem Tensor.PullbackOpen.bilinearOpenPullbackEquiv_apply (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    (P : X.Modules) (β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P) :
    Tensor.PullbackOpen.bilinearOpenPullbackEquiv f M N P β = Tensor.PullbackComparison.bilinearPullbackUnit f M N P β := by
  change ((β.precomp ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N).hom).pushforward f).precomp
      ((Scheme.Modules.restrictAdjunction f).unit.app M)
      ((Scheme.Modules.restrictAdjunction f).unit.app N) = _
  rw [Bilinear.Sheaves.SheafBilinearMap.pushforward_precomp, Bilinear.Sheaves.SheafBilinearMap.precomp_comp]
  exact congrArg₂ (fun a b => (β.pushforward f).precomp a b)
    ((Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) M)
    ((Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) N)

theorem Tensor.PullbackOpen.tensorPullbackComparison_homEquiv (f : X ⟶ Y) (M N : Y.Modules) (P : X.Modules)
    (h : Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶ P) :
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (Tensor.PullbackComparison.tensorPullbackComparison f M N ≫ h)) =
      Tensor.PullbackComparison.bilinearPullbackUnit f M N P
        (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ P h) := by
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, Tensor.PullbackComparison.tensorPullbackComparison_spec,
    ← Tensor.PullbackComparison.bilinearPullbackUnit_postcomp, Tensor.Bifunctor.tensorBilinear_postcomp]

theorem Tensor.PullbackOpen.tensorPullbackComparison_isIso_of_bilinearUnit (f : X ⟶ Y) (M N : Y.Modules)
    (h : ∀ P : X.Modules, Function.Bijective (Tensor.PullbackComparison.bilinearPullbackUnit f M N P)) :
    IsIso (Tensor.PullbackComparison.tensorPullbackComparison f M N) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro P
  let e := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ P).trans
    (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _)
  apply (e.bijective.of_comp_iff' _).mp
  change Function.Bijective (fun a => e (Tensor.PullbackComparison.tensorPullbackComparison f M N ≫ a))
  have he : (fun a => e (Tensor.PullbackComparison.tensorPullbackComparison f M N ≫ a)) =
      fun a => Tensor.PullbackComparison.bilinearPullbackUnit f M N P (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ P a) := by
    funext a
    exact Tensor.PullbackOpen.tensorPullbackComparison_homEquiv f M N P a
  rw [he]
  exact (h P).comp (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ P).bijective

instance Tensor.PullbackOpen.tensorPullbackComparison_open_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f M N) := by
  apply Tensor.PullbackOpen.tensorPullbackComparison_isIso_of_bilinearUnit
  intro P
  have h : Tensor.PullbackComparison.bilinearPullbackUnit f M N P = Tensor.PullbackOpen.bilinearOpenPullbackEquiv f M N P := by
    funext β
    exact (Tensor.PullbackOpen.bilinearOpenPullbackEquiv_apply f M N P β).symm
  rw [h]
  exact (Tensor.PullbackOpen.bilinearOpenPullbackEquiv f M N P).bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
