import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFiberIsoTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareLine
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

/-! # Symmetry Fibers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryFibers.Construction

noncomputable section

/-! A symmetry of the actual polarization family line induces the
corresponding symmetry between original Poincare fibers, with its full
geometric pullback law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme)

def poincareSymmetrySource : A.scheme ⊗ A.scheme ⟶ D.abelian.scheme ⊗ A.scheme :=
  (β_ A.scheme A.scheme).hom ≫ (φ ⊗ₘ 𝟙 A.scheme)

theorem poincareSymmetrySource_point {T : Over S} (x y : T ⟶ A.scheme) :
    lift x y ≫ poincareSymmetrySource D φ = lift (y ≫ φ) x := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [poincareSymmetrySource, Category.assoc, tensorHom_fst, tensorHom_snd,
      Category.comp_id, braiding_hom_fst_assoc, braiding_hom_snd, lift_fst, lift_snd, lift_snd_assoc]

theorem poincareSymmetryTarget_point {T : Over S} (x y : T ⟶ A.scheme) :
    lift x y ≫ (φ ⊗ₘ 𝟙 A.scheme) = lift (x ≫ φ) y := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id, lift_fst_assoc, lift_fst, lift_snd]

variable (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
  (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)

def poincareGlobalSymmetry : Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareSymmetrySource D φ) ≅
    Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ⊗ₘ 𝟙 A.scheme) :=
  (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (β_ A.scheme A.scheme).hom (φ ⊗ₘ 𝟙 A.scheme)
    (poincareSymmetrySource D φ) rfl).symm ≪≫ σ

def poincareSymmetryFiber {T : Over S} (x y : T ⟶ A.scheme) :
    Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (y ≫ φ) x) ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (x ≫ φ) y) :=
  GlobalFiberIsoTransport.Construction.globalFiberIsoTransport (poincareSymmetrySource D φ) (φ ⊗ₘ 𝟙 A.scheme)
    (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareGlobalSymmetry D φ σ) (lift x y)
    (lift (y ≫ φ) x) (lift (x ≫ φ) y)
    (poincareSymmetrySource_point D φ x y) (poincareSymmetryTarget_point D φ x y)

theorem poincareSymmetryFiber_pullback {T T' : Over S} (f : T' ⟶ T) (x y : T ⟶ A.scheme)
    (x' y' : T' ⟶ A.scheme) (hx : f ≫ x = x') (hy : f ≫ y = y')
    (hl : f ≫ lift (y ≫ φ) x = lift (y' ≫ φ) x')
    (hr : f ≫ lift (x ≫ φ) y = lift (x' ≫ φ) y') :
    (Scheme.Modules.pullback f.left).mapIso (poincareSymmetryFiber D φ σ x y) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f (lift (x ≫ φ) y) (lift (x' ≫ φ) y') hr =
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f (lift (y ≫ φ) x) (lift (y' ≫ φ) x') hl ≪≫
      poincareSymmetryFiber D φ σ x' y' := by
  have hb : f ≫ lift x y = lift x' y' := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd, hx, hy]
  exact GlobalFiberIsoTransport.Construction.globalFiberIsoTransport_pullback (poincareSymmetrySource D φ) (φ ⊗ₘ 𝟙 A.scheme)
    (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareGlobalSymmetry D φ σ) f (lift x y) _ _
    (poincareSymmetrySource_point D φ x y) (poincareSymmetryTarget_point D φ x y) (lift x' y') _ _
    (poincareSymmetrySource_point D φ x' y') (poincareSymmetryTarget_point D φ x' y') hb hl hr

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryFibers.Construction
