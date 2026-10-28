import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.OppositeTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ClassPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes

/-! # Opposite Translations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.OppositeTranslations

noncomputable section

/-! Opposite rational-point translations of a Poincare graph bundle tensor
to its square. The constant factor is trivialized on the ground-field point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]

theorem polarizationPairClass_basePoints_eq_one
    (a b : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    Polarization.ClassPairing.polarizationPairClass D p (𝟙_ (Over (Spec (.of K)))) a b = 1 := by
  let : Subsingleton (𝟙_ (Over (Spec (.of K)))).left := by
    change Subsingleton (Spec (.of K))
    infer_instance
  let : Nonempty (𝟙_ (Over (Spec (.of K)))).left := by
    change Nonempty (Spec (.of K))
    infer_instance
  exact Quotient.sound ⟨(D.poincarePair (a ≫ p) b).trivialization_of_subsingleton⟩

theorem polarizationPairClass_constant_diag_eq_one
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    Polarization.ClassPairing.polarizationPairClass D p A.scheme (toUnit A.scheme ≫ a) (toUnit A.scheme ≫ a) = 1 := by
  have h := Polarization.ClassPairing.polarizationPairClass_naturality D p a a (toUnit A.scheme)
  rw [polarizationPairClass_basePoints_eq_one D p a a] at h
  exact h.symm.trans (Line.Bundles.LineBundle.pullbackClass_trivial (toUnit A.scheme).left)

theorem poincareGraph_oppositeTranslations_class
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    Line.Bundles.LineBundle.classOf (((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (A.basePointTranslation a).left).tensor
      ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (A.basePointTranslation a⁻¹).left)) =
        Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower 2) := by
  let B := Polarization.ClassPairing.polarizationPairClass D p A.scheme
  have hi : B (𝟙 A.scheme) (𝟙 A.scheme) = Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle D p) :=
    (Polarization.ClassPairing.graphPullback_class_eq_pair D p (𝟙 A.scheme)).symm.trans
      (Quotient.sound ⟨(Scheme.Modules.pullbackId A.scheme.left).app (PoincareGraph.Bundles.poincareGraphBundle D p).sheaf⟩)
  have hc : B (toUnit A.scheme ≫ a) (toUnit A.scheme ≫ a) = 1 :=
    polarizationPairClass_constant_diag_eq_one D p a
  rw [Line.Bundles.LineBundle.classOf_tensor, Polarization.ClassPairing.graphPullback_class_eq_pair, Polarization.ClassPairing.graphPullback_class_eq_pair,
    Line.Bundles.LineBundle.classOf_tensorPower]
  change B (A.basePointTranslation a) (A.basePointTranslation a) *
    B (A.basePointTranslation a⁻¹) (A.basePointTranslation a⁻¹) = _
  simp only [Abelian.Schemes.AbelianScheme.basePointTranslation, GrpObj.comp_inv]
  rw [Bilinear.OppositeTranslations.bilinear_opposite_translation_diagonal, hi, hc, one_pow, mul_one]

def poincareGraphOppositeTranslationsIso
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    (((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (A.basePointTranslation a).left).tensor
      ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (A.basePointTranslation a⁻¹).left)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower 2).sheaf :=
  (Quotient.exact (poincareGraph_oppositeTranslations_class D p a)).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.OppositeTranslations
