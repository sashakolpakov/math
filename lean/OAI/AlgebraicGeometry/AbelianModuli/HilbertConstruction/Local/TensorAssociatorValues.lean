import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociatorComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerValues

/-! # Tensor Associator Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociatorValues

noncomputable section

/-! Ambient values of local associators are independent of frames and stable under open refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} {L M N : Y.Modules}

def localTensorAssociatorValue (f : X ⟶ Y) [IsOpenImmersion f]
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (r : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    Γ(Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N, U) →ₗ[Γ(Y, U)] Γ(Tensor.ProductSheaf.tensorModule L (Tensor.ProductSheaf.tensorModule M N), U) :=
  OpenPullback.ModuleValues.openPullbackModuleValue f (TensorAssociator.localTensorAssociatorIso f e.hom t.hom r.hom).hom U hU

theorem localTensorAssociatorValue_independent (f : X ⟶ Y) [IsOpenImmersion f]
    (e e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (t t' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (r r' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    localTensorAssociatorValue f e t r U hU = localTensorAssociatorValue f e' t' r' U hU := by
  unfold localTensorAssociatorValue
  rw [TensorAssociator.localTensorAssociatorIso_independent f e.hom e'.hom t.hom t'.hom r.hom r'.hom]

theorem localTensorAssociatorValue_congr {f f' : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion f']
    (h : f = f')
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj L)
    (t : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (t' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj M)
    (r : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj N)
    (r' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) (hU' : U ≤ f'.opensRange) :
    localTensorAssociatorValue f e t r U hU = localTensorAssociatorValue f' e' t' r' U hU' := by
  subst f'
  exact localTensorAssociatorValue_independent f e e' t t' r r' U hU

theorem refine_localTensorAssociator
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] {P Q R : Z.Modules}
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P)
    (t : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj Q)
    (r : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj R) :
    OpenPullback.Refinement.refineOpenPullbackMap f g (TensorAssociator.localTensorAssociatorIso g e.hom t.hom r.hom).hom =
      (TensorAssociator.localTensorAssociatorIso (f ≫ g) (TensorPowerValues.refinedPullbackFrame f g e).hom
        (TensorPowerValues.refinedPullbackFrame f g t).hom (TensorPowerValues.refinedPullbackFrame f g r).hom).hom := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp f g).app (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule P Q) R)).hom).mp
  change _ ≫ ((Scheme.Modules.pullbackComp f g).inv.app _ ≫ _ ≫ _) = _
  exact (((Scheme.Modules.pullbackComp f g).app (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule P Q) R)).hom_inv_id_assoc _).trans
    (TensorAssociatorComposition.localTensorAssociatorIso_comp f g e.hom t.hom r.hom)

theorem localTensorAssociatorValue_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] {P Q R : Z.Modules}
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P)
    (t : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj Q)
    (r : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj R)
    (U : Z.Opens) (hU : U ≤ (f ≫ g).opensRange) :
    localTensorAssociatorValue (f ≫ g) (TensorPowerValues.refinedPullbackFrame f g e) (TensorPowerValues.refinedPullbackFrame f g t)
      (TensorPowerValues.refinedPullbackFrame f g r) U hU =
      localTensorAssociatorValue g e t r U (hU.trans (by
        rw [Scheme.Hom.opensRange_comp]
        exact g.image_le_opensRange f.opensRange)) := by
  unfold localTensorAssociatorValue
  rw [← refine_localTensorAssociator]
  exact OpenPullback.RefinementNaturality.openPullbackModuleValue_comp f g _ U hU

theorem localTensorAssociatorValue_restriction (f : X ⟶ Y) [IsOpenImmersion f]
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (r : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    OpenModule.MapValues.openModuleMapValue f (TensorAssociator.localTensorAssociatorRestrictionIso f e.hom t.hom r.hom).hom U hU =
      localTensorAssociatorValue f e t r U hU :=
  OpenPullback.ModuleValues.openPullbackModuleValue_restriction f (TensorAssociator.localTensorAssociatorIso f e.hom t.hom r.hom).hom U hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociatorValues
