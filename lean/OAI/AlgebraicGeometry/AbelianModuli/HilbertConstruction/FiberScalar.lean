import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Localization

/-! # Fiber Scalar -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberScalar.FiberScalarMaps

noncomputable section

/-! The scalar map of an actual scheme fiber is evaluation through the
local ring, and that local ring is flat over an affine base's functions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

variable (S : Scheme.{u}) (x : S)

theorem fromStalk_appTop : (S.fromSpecStalk x).appTop =
    S.presheaf.germ ⊤ x trivial ≫ (Scheme.ΓSpecIso (S.presheaf.stalk x)).inv := by
  rw [Scheme.fromSpecStalk_appTop]
  simp

theorem fromResidue_appTop : (S.fromSpecResidueField x).appTop ≫
    (Scheme.ΓSpecIso (S.residueField x)).hom = S.Γevaluation x := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, fromStalk_appTop]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rfl

theorem stalk_flat [IsAffine S] : letI : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
    (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
    Module.Flat Γ(S, ⊤) (S.presheaf.stalk x) := by
  let : Algebra Γ(S, ⊤) (S.presheaf.stalk x) := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have := (isAffineOpen_top S).isLocalization_stalk ⟨x, trivial⟩
  exact IsLocalization.flat (S.presheaf.stalk x)
    ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberScalar.FiberScalarMaps
