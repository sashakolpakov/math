import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.OriginFrames
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin

/-! # Scalar Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarLine.Construction

noncomputable section

section

/-! Multiplication by n in either coordinate of the original Poincare
bundle gives canonically isomorphic lines, normalized in the common
origin frame. This compares actual sheaves rather than only line classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) [IsMonHom t] [IsMonHom a] (n : ℕ)

omit [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  [IsMonHom t] [IsMonHom a] in
theorem poincareScalarLine_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ProductIsomorphisms.Construction.poincarePointLine D (t ^ n) a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ProductIsomorphisms.Construction.poincarePointLine D t (a ^ n)) :=
  (PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass_pow_left D t a n).trans
    (PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass_pow_right D t a n).symm

theorem existsUnique_normalizedPoincareScalarComparison :
    ∃! e : (ProductIsomorphisms.Construction.poincarePointLine D (t ^ n) a).sheaf ≅ (ProductIsomorphisms.Construction.poincarePointLine D t (a ^ n)).sheaf,
      (Scheme.Modules.pullback η[T].left).mapIso e =
        (OriginFrames.Construction.poincarePointOriginFrame D (t ^ n) a).symm ≪≫ OriginFrames.Construction.poincarePointOriginFrame D t (a ^ n) := by
  have : IsIso η[T].left.appTop := ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso η[T].left
    (ProductIsomorphisms.Construction.poincarePointLine D (t ^ n) a) (ProductIsomorphisms.Construction.poincarePointLine D t (a ^ n))
    (Classical.choice (Quotient.exact (poincareScalarLine_class D t a n)))
    ((OriginFrames.Construction.poincarePointOriginFrame D (t ^ n) a).symm ≪≫ OriginFrames.Construction.poincarePointOriginFrame D t (a ^ n))

def normalizedPoincareScalarComparison :
    (ProductIsomorphisms.Construction.poincarePointLine D (t ^ n) a).sheaf ≅ (ProductIsomorphisms.Construction.poincarePointLine D t (a ^ n)).sheaf :=
  Classical.choose (existsUnique_normalizedPoincareScalarComparison D t a n)

theorem normalizedPoincareScalarComparison_origin :
    (Scheme.Modules.pullback η[T].left).mapIso (normalizedPoincareScalarComparison D t a n) =
      (OriginFrames.Construction.poincarePointOriginFrame D (t ^ n) a).symm ≪≫ OriginFrames.Construction.poincarePointOriginFrame D t (a ^ n) :=
  (Classical.choose_spec (existsUnique_normalizedPoincareScalarComparison D t a n)).1

end

section

/-! The normalized scalar comparison on the universal Poincare product
parameter is a genuine global sheaf isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

local instance poincareScalarParameter_smooth : Smooth (D.abelian.scheme ⊗ A.scheme).hom := by
  dsimp
  infer_instance

local instance poincareScalarParameter_proper : IsProper (D.abelian.scheme ⊗ A.scheme).hom := by
  dsimp
  infer_instance

local instance poincareScalarParameter_connected : GeometricallyConnected (D.abelian.scheme ⊗ A.scheme).hom :=
  GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst D.abelian.scheme.hom A.scheme.hom) D.abelian.scheme.hom

def poincareGlobalScalarComparison (n : ℕ) :
    (ProductIsomorphisms.Construction.poincarePointLine D ((fst D.abelian.scheme A.scheme) ^ n) (snd D.abelian.scheme A.scheme)).sheaf ≅
      (ProductIsomorphisms.Construction.poincarePointLine D (fst D.abelian.scheme A.scheme) ((snd D.abelian.scheme A.scheme) ^ n)).sheaf := by
  have : CompactSpace (D.abelian.scheme ⊗ A.scheme).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.abelian.scheme ⊗ A.scheme).hom
  have : QuasiSeparatedSpace (D.abelian.scheme ⊗ A.scheme).left :=
    quasiSeparatedSpace_of_quasiSeparated (D.abelian.scheme ⊗ A.scheme).hom
  exact normalizedPoincareScalarComparison D (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) n

end

/-! Pulling the universal normalized comparison to any test scheme
compares the actual Poincare fibers with n in either coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ)
  {T : Over (Spec (.of k))} (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme)

omit [IsAlgClosed k] in
theorem poincareScalarParameter_left :
    lift t a ≫ lift ((fst D.abelian.scheme A.scheme) ^ n) (snd D.abelian.scheme A.scheme) = lift (t ^ n) a := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, lift_fst, lift_snd, MonObj.comp_pow]

omit [IsAlgClosed k] in
theorem poincareScalarParameter_right :
    lift t a ≫ lift (fst D.abelian.scheme A.scheme) ((snd D.abelian.scheme A.scheme) ^ n) = lift t (a ^ n) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, lift_fst, lift_snd, MonObj.comp_pow]

def poincareScalarFiberComparison :
    Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (t ^ n) a) ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift t (a ^ n)) :=
  (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift t a)
    (lift ((fst D.abelian.scheme A.scheme) ^ n) (snd D.abelian.scheme A.scheme)) (lift (t ^ n) a)
    (poincareScalarParameter_left D n t a)).symm ≪≫
      (Scheme.Modules.pullback (lift t a).left).mapIso (poincareGlobalScalarComparison D n) ≪≫
        Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift t a)
          (lift (fst D.abelian.scheme A.scheme) ((snd D.abelian.scheme A.scheme) ^ n)) (lift t (a ^ n))
          (poincareScalarParameter_right D n t a)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarLine.Construction
