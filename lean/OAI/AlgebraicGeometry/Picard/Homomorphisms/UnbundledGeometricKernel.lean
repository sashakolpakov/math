import OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricSheafification
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup

/-! # Unbundled Geometric Kernel -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGeometricKernel

noncomputable section

/-! Geometric duality and Picard kernels without a global dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
variable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)

def poincareLineClass {T : Over S} (x : T ⟶ D.abelian) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((T ⊗ A).left) :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (x ▷ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

theorem poincareLineClass_injective (T : Over S) :
    Function.Injective (poincareLineClass D (T := T)) := by
  intro x y hxy
  apply UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_injective D T
  exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T)) hxy

theorem poincareClass_one (T : Over S) :
    UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (1 : T ⟶ D.abelian) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  rw [UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation, D.origin, UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one,
    RelativeGroup.Construction.trivialPicardClass_eq_one]
  exact (UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply A T 1).symm.trans
    (UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T).map_one

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (E : UnbundledDualData.Construction.UnbundledPicard.DualData B)
variable (f : A ⟶ B) [IsMonHom f]

theorem geometric_dualKernel_trivializes_line
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian)
    (hx : x ≫ UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.mk (𝟙 (Spec (.of k)))) ◁ f).left
        (poincareLineClass E x) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.mk (𝟙 (Spec (.of k))) ⊗ A).left) := by
  apply (GeometricSheafification.Construction.toSheafify_algClosed_bijective k (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A)).injective
  have h := (SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply f
    (Over.mk (𝟙 (Spec (.of k)))) (poincareLineClass E x)).symm
  exact h.trans ((UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback_poincare D E f x).symm.trans
    ((congrArg (UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D) hx).trans (poincareClass_one D _)))

/-- An embedding into the kernel of pullback on actual isomorphism classes. -/
def geometricDualKernelLineEmbedding :
    {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian //
      x ≫ UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f = 1} ↪
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((Over.mk (𝟙 (Spec (.of k))) ⊗ B).left) //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.mk (𝟙 (Spec (.of k)))) ◁ f).left q =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.mk (𝟙 (Spec (.of k))) ⊗ A).left)} where
  toFun x := ⟨poincareLineClass E x.val, geometric_dualKernel_trivializes_line D E f x.val x.property⟩
  inj' _ _ hxy := Subtype.ext ((poincareLineClass_injective E _)
    (congrArg Subtype.val hxy))

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGeometricKernel
