import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IsomorphismPullbackFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Automorphisms Finite Over Field -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismsFiniteOverField

noncomputable section

/-! Actual polarized full-level automorphisms form a finite set over every field, by faithful base change to an algebraic closure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem polarizedAutomorphisms_finite_overField : Finite (Moduli.Isomorphisms.LevelPreservingIso A A) := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let f := Spec.map φ
  have : Flat f := Smooth.FieldExtensionReflection.fieldSpecMap_flat φ
  have : Surjective f := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  have : QuasiCompact f := inferInstanceAs (QuasiCompact (Spec.map φ))
  have : Finite (Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback f)) :=
    AutomorphismsFinite.polarizedAutomorphisms_finite_overAlgClosed (A.pullback f)
  exact Finite.of_injective (fun e : Moduli.Isomorphisms.LevelPreservingIso A A => e.pullback f)
    (Moduli.Isomorphisms.LevelPreservingIso.pullback_injective f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismsFiniteOverField
