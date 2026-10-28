import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityOverClosed
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IsomorphismPullbackFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Rigidity Over Field -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Faithful algebraic-closure base change proves full-level polarized automorphism rigidity over every field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem Level.RigidityOverField.polarizedAutomorphisms_subsingleton_overField (hN : 3 ≤ N) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso A A) := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let f := Spec.map φ
  have : Flat f := Smooth.FieldExtensionReflection.fieldSpecMap_flat φ
  have : Surjective f := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  have : QuasiCompact f := inferInstanceAs (QuasiCompact (Spec.map φ))
  have : Subsingleton (Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback f)) :=
    Level.RigidityOverClosed.polarizedAutomorphisms_subsingleton_overAlgClosed (A.pullback f) hN
  exact (Moduli.Isomorphisms.LevelPreservingIso.pullback_injective f).subsingleton

theorem Moduli.Isomorphisms.LevelPreservingIso.eq_refl_overField (e : Moduli.Isomorphisms.LevelPreservingIso A A) (hN : 3 ≤ N) :
    e = Moduli.Isomorphisms.LevelPreservingIso.refl A := by
  have := Level.RigidityOverField.polarizedAutomorphisms_subsingleton_overField A hN
  exact Subsingleton.elim _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
