import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFieldPointDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Unramified Geometric Point Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedGeometricPointDetection

noncomputable section

/-! Maps to a formally unramified relative scheme are detected by algebraically closed field-valued points, over arbitrary bases. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem unramified_overHom_eq_of_geometricFieldPoints {S : Scheme.{u}} {T M : Over S}
    [LocallyOfFiniteType M.hom] [FormallyUnramified M.hom] (a b : T ⟶ M)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ T.left),
      s ≫ a.left = s ≫ b.left) : a = b := by
  apply UnramifiedFieldPointDetection.unramified_overHom_eq_of_fieldPoints a b
  intro K _ s
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  have : Flat (Spec.map φ) := Smooth.FieldExtensionReflection.fieldSpecMap_flat φ
  have : Surjective (Spec.map φ) := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  have : Epi (Spec.map φ) := Flat.epi_of_flat_of_surjective (Spec.map φ)
  apply (cancel_epi (Spec.map φ)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((h (AlgebraicClosure K) (Spec.map φ ≫ s)).trans (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedGeometricPointDetection
