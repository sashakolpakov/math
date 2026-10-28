import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.OriginFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

/-! # Bilinear Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts.Construction

noncomputable section

/-!
The normalized actual Poincare tensor isomorphisms give bilinear sheaf
products. Their pullbacks to the origin multiply the original frames.
All tensor and unit comparisons here are the ones used by PoincareBundle's
geometric pullback of bilinear maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

def bilinearOfLineIso {X : Scheme.{u}} {M N P : X.Modules} (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P := AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P e.hom

theorem bilinearOfLineIso_toHom {X : Scheme.{u}} {M N P : X.Modules} (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P) :
    Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (bilinearOfLineIso e) = e.hom :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).symm_apply_apply e.hom

instance bilinearOfLineIso_isIso {X : Scheme.{u}} {M N P : X.Modules} (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P) :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (bilinearOfLineIso e)) := by
  rw [bilinearOfLineIso_toHom]
  infer_instance

def framedLineProduct {X : Scheme.{u}} {M N P : X.Modules}
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P :=
  Picard.PoincareBundle.Bilinear.Transport.transport (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) l m n

theorem framedLineProduct_toHom {X : Scheme.{u}} {M N P : X.Modules}
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P) :
    Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (framedLineProduct l m n) =
      (Picard.PoincareBundle.Tensor.UnitPullback.tensorIso l.symm m.symm).hom ≫
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom ≫ n.hom := by
  rw [framedLineProduct, Picard.PoincareBundle.Bilinear.Transport.toHom_transport]
  have hu : Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) =
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom := by
    unfold Picard.PoincareBundle.Bilinear.BilinearPullback.toHom
    exact (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm_apply_eq.mpr (Picard.PoincareBundle.Tensor.UnitPullback.tensorUnitLeft_bilinear _).symm
  rw [hu]
  rfl

theorem framedLineProduct_value {X : Scheme.{u}} {M N P : X.Modules}
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P)
    (U : X.Opens) (a b : Γ(X, U)) :
    (framedLineProduct l m n).app U (l.hom.app U a) (m.hom.app U b) = n.hom.app U (a * b) := by
  have hl := Picard.PoincareBundle.Bilinear.AlgebraTransport.inv_hom_app l U a
  have hm := Picard.PoincareBundle.Bilinear.AlgebraTransport.inv_hom_app m U b
  exact congrArg (fun c : Γ(AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X, U) => n.hom.app U c)
    (congrArg₂ (fun r s : Γ(AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X, U) => (show Γ(X, U) from r) • s) hl hm)

theorem normalizedLineProduct_pullback {X Y : Scheme.{u}} (p : X ⟶ Y)
    (L M N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback p).obj L.sheaf)
    (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback p).obj M.sheaf)
    (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback p).obj N.sheaf)
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf ≅ N.sheaf)
    (he : (Scheme.Modules.pullback p).mapIso e = ProductIsomorphisms.Construction.lineTensorFrameComparison p L M N l m n) :
    Picard.PoincareBundle.Bilinear.BilinearPullback.pullback p (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (bilinearOfLineIso e) =
      framedLineProduct l m n := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change Picard.PoincareBundle.Bilinear.BilinearPullback.toHom _ = Picard.PoincareBundle.Bilinear.BilinearPullback.toHom _
  rw [Picard.PoincareBundle.Bilinear.BilinearPullback.toHom_pullback, framedLineProduct_toHom]
  unfold Picard.PoincareBundle.Bilinear.BilinearPullback.pulledHom
  rw [bilinearOfLineIso_toHom]
  have heh : (Scheme.Modules.pullback p).map e.hom =
      (ProductIsomorphisms.Construction.lineTensorFrameComparison p L M N l m n).hom := congrArg Iso.hom he
  rw [heh]
  change (Picard.PoincareBundle.Tensor.LinePullback.pullbackIso p L.sheaf M.sheaf
      (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)).inv ≫
    (Picard.PoincareBundle.Tensor.LinePullback.pullbackIso p L.sheaf M.sheaf
      (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)).hom ≫
    (Picard.PoincareBundle.Tensor.UnitPullback.tensorIso l.symm m.symm).hom ≫
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom ≫ n.hom = _
  exact Iso.inv_hom_id_assoc _ _

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

attribute [local instance] OriginFrames.Construction.poincareGroupMapMul_isMonHom

def normalizedPoincareBilinearLeft (t v : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom v] [IsMonHom a] :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (ProductIsomorphisms.Construction.poincarePointLine D t a).sheaf (ProductIsomorphisms.Construction.poincarePointLine D v a).sheaf
      (ProductIsomorphisms.Construction.poincarePointLine D (t * v) a).sheaf :=
  bilinearOfLineIso (OriginFrames.Construction.normalizedPoincareProductLeft D t v a)

instance normalizedPoincareBilinearLeft_isIso (t v : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom v] [IsMonHom a] :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (normalizedPoincareBilinearLeft D t v a)) :=
  bilinearOfLineIso_isIso _

theorem normalizedPoincareBilinearLeft_origin (t v : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom v] [IsMonHom a] :
    Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left
      (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (ProductIsomorphisms.Construction.poincarePointLine D t a)) (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (ProductIsomorphisms.Construction.poincarePointLine D v a))
      (normalizedPoincareBilinearLeft D t v a) =
        framedLineProduct (OriginFrames.Construction.poincarePointOriginFrame D t a) (OriginFrames.Construction.poincarePointOriginFrame D v a)
          (OriginFrames.Construction.poincarePointOriginFrame D (t * v) a) :=
  normalizedLineProduct_pullback η[T].left _ _ _ _ _ _ _ (OriginFrames.Construction.normalizedPoincareProductLeft_origin D t v a)

def normalizedPoincareBilinearRight (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom a] [IsMonHom b] :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (ProductIsomorphisms.Construction.poincarePointLine D t a).sheaf (ProductIsomorphisms.Construction.poincarePointLine D t b).sheaf
      (ProductIsomorphisms.Construction.poincarePointLine D t (a * b)).sheaf :=
  bilinearOfLineIso (OriginFrames.Construction.normalizedPoincareProductRight D t a b)

instance normalizedPoincareBilinearRight_isIso (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom a] [IsMonHom b] :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (normalizedPoincareBilinearRight D t a b)) :=
  bilinearOfLineIso_isIso _

theorem normalizedPoincareBilinearRight_origin (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom a] [IsMonHom b] :
    Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left
      (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (ProductIsomorphisms.Construction.poincarePointLine D t a)) (ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (ProductIsomorphisms.Construction.poincarePointLine D t b))
      (normalizedPoincareBilinearRight D t a b) =
        framedLineProduct (OriginFrames.Construction.poincarePointOriginFrame D t a) (OriginFrames.Construction.poincarePointOriginFrame D t b)
          (OriginFrames.Construction.poincarePointOriginFrame D t (a * b)) :=
  normalizedLineProduct_pullback η[T].left _ _ _ _ _ _ _ (OriginFrames.Construction.normalizedPoincareProductRight_origin D t a b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts.Construction
