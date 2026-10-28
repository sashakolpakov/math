import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupPoints
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Split Group Scheme -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupScheme.CM

noncomputable section

/-! A split retraction of commutative group objects is the product of
its scheme-theoretic kernel and its target, on every test object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
  (r : A ⟶ B) [IsMonHom r] (s : B ⟶ A) [IsMonHom s] (hrs : s ≫ r = 𝟙 B)

include hrs

omit [BraidedCategory C] [HasPullbacks C] [IsCommMonObj A] [IsCommMonObj B] in
theorem points_retraction (T : C) (b : T ⟶ B) : Picard.PoincareBundle.Kernel.Scheme.pointsMap r T (Picard.PoincareBundle.Kernel.Scheme.pointsMap s T b) = b :=
  (Category.assoc b s r).trans ((congrArg (b ≫ ·) hrs).trans (Category.comp_id b))

def pointsEquiv (T : C) : (T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject r ⊗ B) ≃ (T ⟶ A) :=
  homEquivToProd.trans
    ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv r T).prodCongr (Equiv.refl (T ⟶ B))) |>.trans
      (SplitGroupPoints.CM.productEquiv (Picard.PoincareBundle.Kernel.Scheme.pointsMap r T) (Picard.PoincareBundle.Kernel.Scheme.pointsMap s T)
        (points_retraction r s hrs T)).toEquiv

theorem pointsEquiv_apply (T : C) (x : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject r ⊗ B) :
    pointsEquiv r s hrs T x =
      (x ≫ fst _ _ ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r) * (x ≫ snd _ _ ≫ s) := by
  change ((x ≫ fst _ _) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r) * ((x ≫ snd _ _) ≫ s) = _
  exact congrArg₂ (· * ·) (Category.assoc _ _ _) (Category.assoc _ _ _)

theorem pointsEquiv_naturality {T U : C} (a : T ⟶ U) (x : U ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject r ⊗ B) :
    pointsEquiv r s hrs T (a ≫ x) = a ≫ pointsEquiv r s hrs U x := by
  rw [pointsEquiv_apply, pointsEquiv_apply, MonObj.comp_mul]
  simp only [Category.assoc]

def productIso : Picard.PoincareBundle.Kernel.Scheme.kernelObject r ⊗ B ≅ A :=
  Yoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun T => (pointsEquiv r s hrs T.unop).toIso)
    (fun a => by ext x; exact pointsEquiv_naturality r s hrs a.unop x))

theorem productIso_hom :
    (productIso r s hrs).hom = (fst _ _ ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r) * (snd _ _ ≫ s) := by
  change pointsEquiv r s hrs _ (𝟙 _) = _
  simpa only [Category.id_comp] using pointsEquiv_apply r s hrs _ (𝟙 _)

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

instance productIso_isMonHom : IsMonHom (productIso r s hrs).hom := by
  rw [productIso_hom, Hom.mul_def]
  infer_instance

def productGroupIso : Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject r ⊗ B) ≅ Grp.mk A :=
  Grp.mkIso' (productIso r s hrs)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupScheme.CM
