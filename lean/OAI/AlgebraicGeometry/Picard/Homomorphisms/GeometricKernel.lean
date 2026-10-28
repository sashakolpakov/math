import OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricSheafification
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousGroup

/-! # Geometric Kernel -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricKernel

noncomputable section

/-! A geometric point in the kernel of a represented dual pullback gives
an actual line-bundle class trivialized by the original morphism.
Distinct dual points give distinct line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def poincareLineClass {T : Over S} (x : T ⟶ D.abelian.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((T ⊗ A.scheme).left) :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (x ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

theorem poincareLineClass_injective (T : Over S) :
    Function.Injective (poincareLineClass D (T := T)) := by
  intro x y hxy
  apply PoincareDetection.Construction.poincareClass_injective D T
  exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)) hxy

theorem poincareClass_one (T : Over S) :
    PoincareDetection.Construction.poincareClass D (1 : T ⟶ D.abelian.scheme) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T := by
  rw [PoincareDetection.Construction.poincareClass_eq_representation, D.origin, HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one,
    RelativeGroup.Construction.trivialPicardClass_eq_one]
  exact (HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom_apply A T 1).symm.trans
    (HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom A T).map_one

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem geometric_dualKernel_trivializes_line
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian.scheme)
    (hx : x ≫ DualPullback.Construction.dualPicardPullback D E f = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.mk (𝟙 (Spec (.of k)))) ◁ f).left
        (poincareLineClass E x) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.mk (𝟙 (Spec (.of k))) ⊗ A.scheme).left) := by
  apply (GeometricSheafification.Construction.toSheafify_algClosed_bijective k (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)).injective
  have h := (SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply f
    (Over.mk (𝟙 (Spec (.of k)))) (poincareLineClass E x)).symm
  exact h.trans ((DualPullback.Construction.dualPicardPullback_poincare D E f x).symm.trans
    ((congrArg (PoincareDetection.Construction.poincareClass D) hx).trans (poincareClass_one D _)))

/-- An embedding into the kernel of pullback on actual isomorphism classes. -/
def geometricDualKernelLineEmbedding :
    {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian.scheme //
      x ≫ DualPullback.Construction.dualPicardPullback D E f = 1} ↪
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((Over.mk (𝟙 (Spec (.of k))) ⊗ B.scheme).left) //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.mk (𝟙 (Spec (.of k)))) ◁ f).left q =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.mk (𝟙 (Spec (.of k))) ⊗ A.scheme).left)} where
  toFun x := ⟨poincareLineClass E x.val, geometric_dualKernel_trivializes_line D E f x.val x.property⟩
  inj' _ _ hxy := Subtype.ext ((poincareLineClass_injective E _)
    (congrArg Subtype.val hxy))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricKernel
