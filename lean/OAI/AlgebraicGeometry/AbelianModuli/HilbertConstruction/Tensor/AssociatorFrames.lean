import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameComparison

/-! # Associator Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AssociatorFrames

noncomputable section

/-! The associator on framed module sheaves is independent of the chosen frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M N : X.Modules}

def tensorAssociatorFrameIso
    (e : Line.Bundles.structureModule X ⟶ L) (f : Line.Bundles.structureModule X ⟶ M) (g : Line.Bundles.structureModule X ⟶ N)
    [IsIso e] [IsIso f] [IsIso g] :
    ProductSheaf.tensorModule (ProductSheaf.tensorModule L M) N ≅ ProductSheaf.tensorModule L (ProductSheaf.tensorModule M N) :=
  (asIso (ProductSections.tensorProductSection (ProductSections.tensorProductSection e f) g)).symm ≪≫
    asIso (ProductSections.tensorProductSection e (ProductSections.tensorProductSection f g))

theorem tensorAssociatorFrameIso_frame
    (e : Line.Bundles.structureModule X ⟶ L) (f : Line.Bundles.structureModule X ⟶ M) (g : Line.Bundles.structureModule X ⟶ N)
    [IsIso e] [IsIso f] [IsIso g] :
    ProductSections.tensorProductSection (ProductSections.tensorProductSection e f) g ≫ (tensorAssociatorFrameIso e f g).hom =
      ProductSections.tensorProductSection e (ProductSections.tensorProductSection f g) := by
  change _ ≫ (inv (ProductSections.tensorProductSection (ProductSections.tensorProductSection e f) g) ≫ _) = _
  simp only [IsIso.hom_inv_id_assoc]
  rfl

theorem frameCoordinate_tensorProduct_assoc
    (e s : Line.Bundles.structureModule X ⟶ L) (f t : Line.Bundles.structureModule X ⟶ M) (g r : Line.Bundles.structureModule X ⟶ N)
    [IsIso e] [IsIso f] [IsIso g] :
    Frame.Coordinates.frameCoordinate (ProductSections.tensorProductSection (ProductSections.tensorProductSection e f) g)
      (ProductSections.tensorProductSection (ProductSections.tensorProductSection s t) r) =
      Frame.Coordinates.frameCoordinate (ProductSections.tensorProductSection e (ProductSections.tensorProductSection f g))
        (ProductSections.tensorProductSection s (ProductSections.tensorProductSection t r)) := by
  simp only [SectionCoordinates.frameCoordinate_tensorProduct, mul_assoc]

theorem tensorAssociatorFrameIso_independent
    (e e' : Line.Bundles.structureModule X ⟶ L) (f f' : Line.Bundles.structureModule X ⟶ M) (g g' : Line.Bundles.structureModule X ⟶ N)
    [IsIso e] [IsIso e'] [IsIso f] [IsIso f'] [IsIso g] [IsIso g'] :
    tensorAssociatorFrameIso e f g = tensorAssociatorFrameIso e' f' g' := by
  apply Iso.ext
  exact TensorPower.FrameComparison.frameMap_eq_of_coordinate_eq _ _ _ _ (frameCoordinate_tensorProduct_assoc e e' f f' g g')

theorem tensorAssociatorFrameIso_natural {L' M' N' : X.Modules}
    (e : Line.Bundles.structureModule X ⟶ L) (f : Line.Bundles.structureModule X ⟶ M) (g : Line.Bundles.structureModule X ⟶ N)
    [IsIso e] [IsIso f] [IsIso g]
    (a : L ⟶ L') (b : M ⟶ M') (c : N ⟶ N') [IsIso a] [IsIso b] [IsIso c] :
    Bifunctor.tensorModuleMap (Bifunctor.tensorModuleMap a b) c ≫ (tensorAssociatorFrameIso (e ≫ a) (f ≫ b) (g ≫ c)).hom =
      (tensorAssociatorFrameIso e f g).hom ≫ Bifunctor.tensorModuleMap a (Bifunctor.tensorModuleMap b c) := by
  apply (cancel_epi (ProductSections.tensorProductSection (ProductSections.tensorProductSection e f) g)).mp
  rw [← Category.assoc, ProductSections.tensorProductSection_postcomp, ProductSections.tensorProductSection_postcomp,
    tensorAssociatorFrameIso_frame, ← Category.assoc, tensorAssociatorFrameIso_frame,
    ProductSections.tensorProductSection_postcomp, ProductSections.tensorProductSection_postcomp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AssociatorFrames
