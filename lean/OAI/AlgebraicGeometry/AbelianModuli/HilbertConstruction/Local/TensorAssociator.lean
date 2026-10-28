import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleTensorComposition

/-! # Tensor Associator -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociator

noncomputable section

/-! Frame-independent local associators between pullbacks of the global tensor sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {L M N : Y.Modules}

def localTensorAssociatorIso
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    (r : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj N)
    [IsIso e] [IsIso t] [IsIso r] :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N) ≅
      (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule L (Tensor.ProductSheaf.tensorModule M N)) :=
  TripleTensorPullbacks.leftTripleTensorPullbackIso f L M N ≪≫ Tensor.AssociatorFrames.tensorAssociatorFrameIso e t r ≪≫
    (TripleTensorPullbacks.rightTripleTensorPullbackIso f L M N).symm

theorem localTensorAssociatorIso_spec
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    (r : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj N)
    [IsIso e] [IsIso t] [IsIso r] :
    (localTensorAssociatorIso f e t r).hom ≫ (TripleTensorPullbacks.rightTripleTensorPullbackIso f L M N).hom =
      (TripleTensorPullbacks.leftTripleTensorPullbackIso f L M N).hom ≫ (Tensor.AssociatorFrames.tensorAssociatorFrameIso e t r).hom := by
  simp only [localTensorAssociatorIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem localTensorAssociatorIso_independent
    (e e' : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t t' : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    (r r' : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj N)
    [IsIso e] [IsIso e'] [IsIso t] [IsIso t'] [IsIso r] [IsIso r'] :
    localTensorAssociatorIso f e t r = localTensorAssociatorIso f e' t' r' := by
  unfold localTensorAssociatorIso
  rw [Tensor.AssociatorFrames.tensorAssociatorFrameIso_independent e e' t t' r r']

def localTensorAssociatorRestrictionIso
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    (r : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj N)
    [IsIso e] [IsIso t] [IsIso r] :
    (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N).restrict f ≅
      (Tensor.ProductSheaf.tensorModule L (Tensor.ProductSheaf.tensorModule M N)).restrict f :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app _ ≪≫ localTensorAssociatorIso f e t r ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback f).app _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociator
