import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ScalarCharacters

/-! # Line Kernel Characters -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCharacters

noncomputable section

/-! Characters constructed from actual pullback-trivialized line bundles,
using any native Hopf-coordinate presentation of the finite kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable {f : A ⟶ B} [IsMonHom f]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable [IsAffine (Kernel.Construction.kernelScheme f).left]

theorem kernelScalar_pullback_one (D : KernelScalar.Construction.KernelScalarCocycle f)
    {G : Over (Spec (.of k))} [GrpObj G] (i : G ⟶ Kernel.Construction.kernelScheme f) [IsMonHom i]
    (T : Over (Spec (.of k))) :
    (1 : T ⟶ G).left.appTop (i.left.appTop D.kernelScalar) = 1 := by
  change (i.left.appTop ≫ (1 : T ⟶ G).left.appTop) D.kernelScalar = _
  rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, MonObj.one_comp]
  exact D.kernelScalar_one T

theorem kernelScalar_pullback_mul (D : KernelScalar.Construction.KernelScalarCocycle f)
    {G : Over (Spec (.of k))} [GrpObj G] (i : G ⟶ Kernel.Construction.kernelScheme f) [IsMonHom i]
    (T : Over (Spec (.of k))) (a b : T ⟶ G) :
    (a * b).left.appTop (i.left.appTop D.kernelScalar) =
      a.left.appTop (i.left.appTop D.kernelScalar) *
        b.left.appTop (i.left.appTop D.kernelScalar) := by
  have h := D.kernelScalar_mul (a ≫ i) (b ≫ i)
  rw [← MonObj.mul_comp] at h
  exact h

def kernelCocycleCoordinateCharacter (D : KernelScalar.Construction.KernelScalarCocycle f)
    (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (op R)).X ⟶ Kernel.Construction.kernelScheme f) [IsMonHom i] : GroupLike k R :=
  ScalarCharacters.Construction.groupLikeOfMultiplicativeScalar k R (i.left.appTop D.kernelScalar)
    (kernelScalar_pullback_one D i) (kernelScalar_pullback_mul D i)

def lineKernelCoordinateCharacter (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (op R)).X ⟶ Kernel.Construction.kernelScheme f) [IsMonHom i] : GroupLike k R :=
  kernelCocycleCoordinateCharacter (LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e) R i

theorem kernelCocycleCoordinateCharacter_eq_implies_scalar_eq
    (D E : KernelScalar.Construction.KernelScalarCocycle f) (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (op R)).X ≅ Kernel.Construction.kernelScheme f) [IsMonHom i.hom]
    (h : kernelCocycleCoordinateCharacter D R i.hom =
      kernelCocycleCoordinateCharacter E R i.hom) : D.kernelScalar = E.kernelScalar := by
  have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map i.hom))
  have : IsIso i.hom.left.appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map i.hom.left.op))
  have hs : i.hom.left.appTop D.kernelScalar = i.hom.left.appTop E.kernelScalar :=
    ScalarCharacters.Construction.groupLikeOfMultiplicativeScalar_injective _ _ _ _ _ _ h
  exact (ConcreteCategory.bijective_of_isIso i.hom.left.appTop).injective hs

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCharacters
