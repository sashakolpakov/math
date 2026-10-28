import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorPrecomp

/-! # Binary Tensor Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorIs.Construction.BinaryTensorRestriction

noncomputable section

/-! Naturality of the actual binary tensor-sheaf comparison under restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)

def homEquiv (P : X.Modules) :
    ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict f ⟶ P) ≃ AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (M.restrict f) (N.restrict f) P :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N).homEquiv

theorem postcomp {P : X.Modules} (h : (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict f ⟶ P) :
    ((BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear M N).restrict f).postcomp h = BinaryTensorRestriction.homEquiv f M N P h := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N P).injective
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv_postcomp]
  change ((((BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear M N).restrict f).pushforward f).precomp
      ((Scheme.Modules.restrictAdjunction f).unit.app M)
      ((Scheme.Modules.restrictAdjunction f).unit.app N)).postcomp
        ((Scheme.Modules.pushforward f).map h) = _
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrict_unit_naturality, ← AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.postcomp_comp]
  exact (BinaryTensorPrecomp.Construction.BinaryTensorUniversal.postcomp
    ((Scheme.Modules.restrictAdjunction f).homEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P h)).trans
      ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N P).apply_symm_apply _).symm

theorem iso_spec : ((BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear M N).restrict f).postcomp
    (AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso f M N).hom =
      BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear (M.restrict f) (N.restrict f) := by
  rw [BinaryTensorRestriction.postcomp]
  exact (BinaryTensorRestriction.homEquiv f M N _).apply_symm_apply _

theorem hom_ext {P : X.Modules} {a b : (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict f ⟶ P}
    (h : ((BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear M N).restrict f).postcomp a =
      ((BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear M N).restrict f).postcomp b) : a = b := by
  rw [BinaryTensorRestriction.postcomp, BinaryTensorRestriction.postcomp] at h
  exact (BinaryTensorRestriction.homEquiv f M N P).injective h

theorem naturality {M' N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.restrictFunctor f).map (BinaryTensorId.Construction.BinaryTensorMap.map a b) ≫
      (AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso f M' N').hom =
    (AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso f M N).hom ≫
      BinaryTensorId.Construction.BinaryTensorMap.map ((Scheme.Modules.restrictFunctor f).map a)
        ((Scheme.Modules.restrictFunctor f).map b) := by
  apply hom_ext f M N
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, ← AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrict_postcomp,
    BinaryTensorPrecomp.Construction.BinaryTensorUniversal.map_spec, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrict_precomp,
    ← AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, iso_spec,
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, iso_spec, BinaryTensorPrecomp.Construction.BinaryTensorUniversal.map_spec]

theorem isIso_map_iff {M' N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    IsIso ((Scheme.Modules.restrictFunctor f).map (BinaryTensorId.Construction.BinaryTensorMap.map a b)) ↔
      IsIso (BinaryTensorId.Construction.BinaryTensorMap.map ((Scheme.Modules.restrictFunctor f).map a)
        ((Scheme.Modules.restrictFunctor f).map b)) := by
  have he := congrArg (fun z => IsIso z) (naturality f M N a b)
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using he.to_iff

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorIs.Construction.BinaryTensorRestriction
