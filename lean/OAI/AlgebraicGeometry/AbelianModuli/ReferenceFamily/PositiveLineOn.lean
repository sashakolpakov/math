import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback

/-! # Positive Line On -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveLineOn

noncomputable section

/-! The native positive Poincare formula, equivalently expressed in
actual line-bundle classes while retaining its ample bundle and identity frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction

variable {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (Q : HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left)

def PositiveLineFormula : Prop :=
  ∃ L : HilbertConstruction.Line.Bundles.LineBundle A.scheme.left, L.IsAmple ∧
    Nonempty ((L.pullback η[A.scheme].left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule S) ∧
    Nonempty (HilbertConstruction.Tensor.ProductSheaf.tensorModule (HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
      (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)

theorem positiveLineFormula_iff_class : PositiveLineFormula A Q ↔
    ∃ L : HilbertConstruction.Line.Bundles.LineBundle A.scheme.left, L.IsAmple ∧
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback η[A.scheme].left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 ∧
      HilbertConstruction.Line.Bundles.LineBundle.classOf Q * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A.scheme A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A.scheme A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
          Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A.scheme].left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  constructor
  · rintro ⟨L, hL, ⟨e₀⟩, ⟨e₂⟩⟩
    exact ⟨L, hL, Quotient.sound ⟨e₀⟩, Quotient.sound ⟨e₂⟩⟩
  · rintro ⟨L, hL, h₀, h₂⟩
    refine ⟨L, hL, ?_, ?_⟩
    · exact Quotient.exact (s := HilbertConstruction.Line.Bundles.LineBundle.isoSetoid S)
        (a := L.pullback η[A.scheme].left) (b := HilbertConstruction.Line.Bundles.LineBundle.trivial S) h₀
    · exact Quotient.exact (s := HilbertConstruction.Line.Bundles.LineBundle.isoSetoid (A.scheme ⊗ A.scheme).left)
        (a := (Q.tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
          (L.pullback (snd A.scheme A.scheme).left))
        (b := L.pullback μ[A.scheme].left) h₂

theorem positiveOnGeometricFiber_iff_formula (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (K : Type) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) :
    HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K s ↔ PositiveLineFormula (A.pullback s) (HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s) :=
  Iff.rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveLineOn
