import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductIsomorphisms
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareLine
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

/-! # Origin Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.OriginFrames.Construction

noncomputable section

/-!
The original normalization of the Poincare bundle supplies its zero
frame on every test scheme. Pulling that frame to the origin of a group
parameter fixes the horizontal and vertical product isomorphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem poincareZeroSection_comp_one (U : Over S) :
    (1 : U ⟶ A.scheme) ≫ (Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection (Z := D.abelian.scheme) (X := A.scheme)) =
      (1 : U ⟶ D.abelian.scheme ⊗ A.scheme) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection, Category.assoc, lift_fst, lift_snd, MonObj.comp_one, MonObj.one_comp, Category.comp_id]

def poincareZeroFrame (U : Over S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (1 : U ⟶ D.abelian.scheme ⊗ A.scheme) :=
  Picard.PoincareBundle.GlobalPullbackFrame.atPoint (Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection (Z := D.abelian.scheme) (X := A.scheme)) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (Classical.choice D.normalizedAtDualZero).symm (1 : U ⟶ A.scheme) 1 (poincareZeroSection_comp_one D U)

/-- This is the actual pullback law of the frame chosen from the original Poincare normalization. -/
theorem poincareZeroFrame_natural {U V : Over S} (r : V ⟶ U) :
    Picard.PoincareBundle.FrameRatioPullback.pullFrame r.left (poincareZeroFrame D U) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) r 1 1 (MonObj.comp_one r) =
        poincareZeroFrame D V :=
  Picard.PoincareBundle.GlobalFrameNaturality.atPoint_pullback
    (Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection (Z := D.abelian.scheme) (X := A.scheme)) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (Classical.choice D.normalizedAtDualZero).symm r 1 1 (poincareZeroSection_comp_one D U)
    1 1 (poincareZeroSection_comp_one D V) (MonObj.comp_one r) (MonObj.comp_one r)

variable {k : Type} [Field k] [IsAlgClosed k] {d : ℕ}
  {Ab : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} (Db : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData Ab)
  {T : Over (Spec (.of k))} [GrpObj T]

/-- A homomorphism pair pulls the same original zero frame to the origin of its parameter. -/
def poincarePointOriginFrame (t : T ⟶ Db.abelian.scheme) (a : T ⟶ Ab.scheme)
    [IsMonHom t] [IsMonHom a] :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((ProductIsomorphisms.Construction.poincarePointLine Db t a).pullback η[T].left).sheaf :=
  poincareZeroFrame Db _ ≪≫
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison (lift t a) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db) η[T] 1
      (by rw [MonObj.one_eq_one]; exact MonObj.one_comp (lift t a))).symm

local instance poincareGroupMapMul_isMonHom {X Y : Over (Spec (.of k))}
    [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (a b : X ⟶ Y) [IsMonHom a] [IsMonHom b] :
    IsMonHom (a * b) := by
  rw [Hom.mul_def]
  infer_instance

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

/-- The horizontal Poincare product is fixed by the original zero frame. -/
def normalizedPoincareProductLeft (t v : T ⟶ Db.abelian.scheme) (a : T ⟶ Ab.scheme)
    [IsMonHom t] [IsMonHom v] [IsMonHom a] :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (ProductIsomorphisms.Construction.poincarePointLine Db t a).sheaf (ProductIsomorphisms.Construction.poincarePointLine Db v a).sheaf ≅
      (ProductIsomorphisms.Construction.poincarePointLine Db (t * v) a).sheaf :=
  Classical.choose (ProductIsomorphisms.Construction.existsUnique_normalizedPoincareProduct_left Db t v a
    (poincarePointOriginFrame Db t a) (poincarePointOriginFrame Db v a)
    (poincarePointOriginFrame Db (t * v) a))

theorem normalizedPoincareProductLeft_origin (t v : T ⟶ Db.abelian.scheme) (a : T ⟶ Ab.scheme)
    [IsMonHom t] [IsMonHom v] [IsMonHom a] :
    (Scheme.Modules.pullback η[T].left).mapIso (normalizedPoincareProductLeft Db t v a) =
      ProductIsomorphisms.Construction.lineTensorFrameComparison η[T].left _ _ _
        (poincarePointOriginFrame Db t a) (poincarePointOriginFrame Db v a)
        (poincarePointOriginFrame Db (t * v) a) :=
  (Classical.choose_spec (ProductIsomorphisms.Construction.existsUnique_normalizedPoincareProduct_left Db t v a
    (poincarePointOriginFrame Db t a) (poincarePointOriginFrame Db v a)
    (poincarePointOriginFrame Db (t * v) a))).1

/-- The vertical product uses the same original zero frame. -/
def normalizedPoincareProductRight (t : T ⟶ Db.abelian.scheme) (a b : T ⟶ Ab.scheme)
    [IsMonHom t] [IsMonHom a] [IsMonHom b] :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (ProductIsomorphisms.Construction.poincarePointLine Db t a).sheaf (ProductIsomorphisms.Construction.poincarePointLine Db t b).sheaf ≅
      (ProductIsomorphisms.Construction.poincarePointLine Db t (a * b)).sheaf :=
  Classical.choose (ProductIsomorphisms.Construction.existsUnique_normalizedPoincareProduct_right Db t a b
    (poincarePointOriginFrame Db t a) (poincarePointOriginFrame Db t b)
    (poincarePointOriginFrame Db t (a * b)))

theorem normalizedPoincareProductRight_origin (t : T ⟶ Db.abelian.scheme) (a b : T ⟶ Ab.scheme)
    [IsMonHom t] [IsMonHom a] [IsMonHom b] :
    (Scheme.Modules.pullback η[T].left).mapIso (normalizedPoincareProductRight Db t a b) =
      ProductIsomorphisms.Construction.lineTensorFrameComparison η[T].left _ _ _
        (poincarePointOriginFrame Db t a) (poincarePointOriginFrame Db t b)
        (poincarePointOriginFrame Db t (a * b)) :=
  (Classical.choose_spec (ProductIsomorphisms.Construction.existsUnique_normalizedPoincareProduct_right Db t a b
    (poincarePointOriginFrame Db t a) (poincarePointOriginFrame Db t b)
    (poincarePointOriginFrame Db t (a * b)))).1

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.OriginFrames.Construction
