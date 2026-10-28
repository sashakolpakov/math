import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionParameterLine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.ScalarUnitCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperGroupParameterFunctions
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle

/-! # Parameter Kernel Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterKernelCharacter.Construction

noncomputable section

/-! The actual torsion Poincare line and its multiplication-pullback
frame give a kernel character over every affine parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle.Construction

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (n : ℕ) [IsFinite ((𝟙 A.scheme) ^ n).left] [Flat ((𝟙 A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left]

omit [IsAlgClosed k] in
theorem poincareParameterKernel_projection_appTop_isIso
    (Q : Over (Spec (.of k))) [IsAffine Q.left] :
    IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)))
      ((Over.pullback Q.hom).obj A.scheme)).left.appTop := by
  let f := (Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)
  have hf : IsFinite f.left := MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom _ inferInstance
  have hflat : Flat f.left := MorphismProperty.overPullbackMap (P := @Flat) Q.hom _ inferInstance
  have hfp : LocallyOfFinitePresentation f.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) Q.hom _ inferInstance
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f ⟨hf, hflat, hfp⟩).1
  have : IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left := isAffine_of_isAffineHom (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom
  exact ProperGroupParameterFunctions.Construction.properGroup_parameter_product_appTop_isIso A.scheme Q (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)

def poincareParameterKernelCocycle {Q : Over (Spec (.of k))}
    (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1) :
    Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)) :=
  Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle _ (TorsionParameterLine.Construction.poincareTorsionParameterLine D t)
    (TorsionParameterLine.Construction.poincareTorsionParameterPullbackFrame D t n ht).symm

def poincareParameterKernelCharacter {Q : Over (Spec (.of k))} [IsAffine Q.left]
    (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1) (U : Over Q.left) :
    (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) →* Γ(U.left, ⊤)ˣ := by
  have := poincareParameterKernel_projection_appTop_isIso (A := A) n Q
  exact Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (poincareParameterKernelCocycle D n t ht) U

theorem poincareParameterKernelCharacter_recovers {Q : Over (Spec (.of k))} [IsAffine Q.left]
    (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1) {U : Over Q.left}
    (x : U ⟶ (Over.pullback Q.hom).obj A.scheme)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    (poincareParameterKernelCocycle D n t ht).value x z =
      (poincareParameterKernelCharacter D n t ht U z : Γ(U.left, ⊤)) := by
  have := poincareParameterKernel_projection_appTop_isIso (A := A) n Q
  exact Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_recovers (poincareParameterKernelCocycle D n t ht) x z

theorem poincareParameterKernelCharacter_natural {Q : Over (Spec (.of k))} [IsAffine Q.left]
    (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1) {U V : Over Q.left} (a : V ⟶ U)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    Units.map a.left.appTop.hom (poincareParameterKernelCharacter D n t ht U z) =
      poincareParameterKernelCharacter D n t ht V (a ≫ z) := by
  have := poincareParameterKernel_projection_appTop_isIso (A := A) n Q
  exact Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (poincareParameterKernelCocycle D n t ht) a z

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterKernelCharacter.Construction
