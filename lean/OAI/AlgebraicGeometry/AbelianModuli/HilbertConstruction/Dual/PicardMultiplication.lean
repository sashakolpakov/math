import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_

/-! # Picard Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual

noncomputable section

/-! The representing dual carries the multiplication induced by tensor product of homogeneous Picard classes. Comparison with its supplied abelian group law is a separate rigidity question. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {g : ℕ} {S : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

abbrev Data.DualAbelianData.picardMonoid (D : Data.DualAbelianData A) : MonObj D.abelian.scheme :=
  MonObj.ofRepresentableBy D.abelian.scheme
    (A.homogeneousPicardCommMonFunctor ⋙ forget₂ CommMonCat MonCat) D.representable

theorem Data.DualAbelianData.picardMonoid_commutative (D : Data.DualAbelianData A) :
    letI := D.picardMonoid
    IsCommMonObj D.abelian.scheme :=
  IsCommMonObj.ofRepresentableBy D.abelian.scheme A.homogeneousPicardCommMonFunctor D.representable

def Data.DualAbelianData.tensorMultiplication (D : Data.DualAbelianData A) :
    D.abelian.scheme ⊗ D.abelian.scheme ⟶ D.abelian.scheme :=
  D.picardMonoid.mul

theorem Data.DualAbelianData.tensorMultiplication_classifies (D : Data.DualAbelianData A) :
    D.representable.homEquiv D.tensorMultiplication =
      D.representable.homEquiv (fst D.abelian.scheme D.abelian.scheme) *
        D.representable.homEquiv (snd D.abelian.scheme D.abelian.scheme) :=
  D.representable.homEquiv.apply_symm_apply _

theorem Data.DualAbelianData.picardMonoid_one (D : Data.DualAbelianData A) : D.picardMonoid.one = η[D.abelian.scheme] := by
  apply D.representable.homEquiv.injective
  have h₀ : D.representable.homEquiv η[D.abelian.scheme] =
      (1 : A.HomogeneousPicardSections (𝟙_ (Over S))) :=
    (congrArg D.representable.homEquiv (MonObj.one_eq_one (M := D.abelian.scheme))).trans
      ((D.origin _).trans (A.trivialHomogeneousPicardClass_eq_one _))
  exact (D.representable.homEquiv.apply_symm_apply _).trans h₀.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual
