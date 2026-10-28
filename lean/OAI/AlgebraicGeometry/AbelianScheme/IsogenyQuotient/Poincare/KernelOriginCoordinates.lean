import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.ProductPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarFrame

/-! # Kernel Origin Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelOriginCoordinates.Construction

noncomputable section

/-! The zero and torsion coordinates of a parameterized Poincare
kernel scalar, expressed over the original field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {Q : Over (Spec (.of k))}

def poincareParameterDualCoordinate (t : Q ⟶ D.abelian.scheme) (U : Over Q.left) :
    (Over.map Q.hom).obj U ⟶ D.abelian.scheme := CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U ≫ t

theorem poincareParameterDualCoordinate_pow (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1)
    (U : Over Q.left) : (poincareParameterDualCoordinate D t U) ^ n = 1 := by
  rw [poincareParameterDualCoordinate, ← MonObj.comp_pow, ht, MonObj.comp_one]

def poincareParameterKernelCoordinate (n : ℕ) (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    (Over.map Q.hom).obj U ⟶ A.scheme :=
  CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom ((𝟙 A.scheme) ^ n) U z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n)

theorem poincareParameterKernelCoordinate_pow (n : ℕ) (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    (poincareParameterKernelCoordinate n U z) ^ n = 1 := by
  have h : (poincareParameterKernelCoordinate n U z) ≫ ((𝟙 A.scheme) ^ n) = 1 := by
    rw [poincareParameterKernelCoordinate, Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]
  simpa only [MonObj.comp_pow, Category.comp_id] using h

theorem poincareParameterKernelCoordinate_product (n : ℕ) (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) ≫
      snd Q A.scheme = poincareParameterKernelCoordinate n U z :=
  (Parameter.ProductPoints.Construction.parameterProductPoint_snd Q A.scheme U _).trans
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion Q.hom ((𝟙 A.scheme) ^ n) U z).symm

theorem poincareParameterProduct_origin (t : Q ⟶ D.abelian.scheme) (U : Over Q.left) :
    Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U 1 ≫ lift (fst Q A.scheme ≫ t) (snd Q A.scheme) =
      lift (poincareParameterDualCoordinate D t U) 1 := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, Parameter.ProductPoints.Construction.parameterProductPoint_fst]
    rfl
  · simp only [Category.assoc, lift_snd, Parameter.ProductPoints.Construction.parameterProductPoint_snd, map_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelOriginCoordinates.Construction
