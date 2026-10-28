import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorAssociativity

/-! # Tensor Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPullback

noncomputable section

/-! The canonical comparison between pullback of a tensor product and tensor of pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def pushforwardBilinear {M N P : X.Modules} (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) ((Scheme.Modules.pushforward f).obj P) where
  app U :=
    { toFun m :=
        { toFun := (b.app (f ⁻¹ᵁ U) m)
          map_add' n n' := (b.app (f ⁻¹ᵁ U) m).map_add n n'
          map_smul' r n := (b.app (f ⁻¹ᵁ U) m).map_smul (f.app U r) n }
      map_add' m m' := by
        ext n
        exact congrArg (fun c : Γ(N, f ⁻¹ᵁ U) →ₗ[Γ(X, f ⁻¹ᵁ U)] Γ(P, f ⁻¹ᵁ U) => c n)
          ((b.app (f ⁻¹ᵁ U)).map_add m m')
      map_smul' r m := by
        ext n
        exact congrArg (fun c : Γ(N, f ⁻¹ᵁ U) →ₗ[Γ(X, f ⁻¹ᵁ U)] Γ(P, f ⁻¹ᵁ U) => c n)
          ((b.app (f ⁻¹ᵁ U)).map_smul (f.app U r) m) }
  naturality h m n := b.naturality ((TopologicalSpace.Opens.map f.base).map h) m n

def tensorPullbackComparison (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ⟶
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).symm
      ((pushforwardBilinear f (TensorAssociativity.Construction.tensorModuleBilinear
        ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))).precomp
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)))

theorem tensorPullbackComparison_adjunction (M N : Y.Modules) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (tensorPullbackComparison f M N)) =
      (pushforwardBilinear f (TensorAssociativity.Construction.tensorModuleBilinear
        ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))).precomp
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) := by
  rw [tensorPullbackComparison, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPullback
