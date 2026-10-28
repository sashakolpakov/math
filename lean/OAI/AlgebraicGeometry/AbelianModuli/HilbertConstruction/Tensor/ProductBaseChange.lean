import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.BilinearRestriction

/-! # Product Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual tensor product of module sheaves commutes with restriction and open pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Restriction of the tensor sheaf corepresents bilinear maps from the restricted factors. -/
def Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (Bilinear.Sheaves.SheafBilinearMap.outputFunctor (M.restrict f) (N.restrict f)).CorepresentableBy
      ((Tensor.ProductSheaf.tensorModule M N).restrict f) where
  homEquiv {P} := ((Scheme.Modules.restrictAdjunction f).homEquiv (Tensor.ProductSheaf.tensorModule M N) P).trans
    ((Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N ((Scheme.Modules.pushforward f).obj P)).trans
      (Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N P).symm)
  homEquiv_comp {P Q} h a := by
    let eQ := (Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N Q).symm
    exact (congrArg (fun b => eQ (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N
      ((Scheme.Modules.pushforward f).obj Q) b))
      ((Scheme.Modules.restrictAdjunction f).homEquiv_naturality_right a h)).trans
        ((congrArg eQ (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp
          ((Scheme.Modules.restrictAdjunction f).homEquiv (Tensor.ProductSheaf.tensorModule M N) P a)
          ((Scheme.Modules.pushforward f).map h))).trans
            (Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv_symm_postcomp f M N
              (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N ((Scheme.Modules.pushforward f).obj P)
                ((Scheme.Modules.restrictAdjunction f).homEquiv (Tensor.ProductSheaf.tensorModule M N) P a)) h))

/-- Restriction commutes with tensor products of module sheaves. -/
def Tensor.ProductBaseChange.tensorModuleRestrictIso (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (Tensor.ProductSheaf.tensorModule M N).restrict f ≅ Tensor.ProductSheaf.tensorModule (M.restrict f) (N.restrict f) :=
  (Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N).uniqueUpToIso
    (Bilinear.Sheaves.SheafBilinearMap.corepresentable (M.restrict f) (N.restrict f))

/-- The canonical module-sheaf pullback along an open immersion commutes with tensor products. -/
def Tensor.ProductBaseChange.tensorModulePullbackIso (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule M N) ≅
      Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.restrictFunctorIsoPullback f).app (Tensor.ProductSheaf.tensorModule M N)).symm ≪≫
    Tensor.ProductBaseChange.tensorModuleRestrictIso f M N ≪≫
      Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.restrictFunctorIsoPullback f).app M)
        ((Scheme.Modules.restrictFunctorIsoPullback f).app N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
