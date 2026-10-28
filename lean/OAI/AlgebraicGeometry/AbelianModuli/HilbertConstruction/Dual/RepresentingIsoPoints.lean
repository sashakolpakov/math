import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! # Representing Iso Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual

noncomputable section

/-! The canonical comparison of two representing dual abelian schemes preserves every represented Picard point and the identity section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D E : Data.DualAbelianData A)

theorem Data.DualAbelianData.uniqueUnderlyingIso_hom_classifies {T : Over S} (x : T ⟶ D.abelian.scheme) :
    E.representable.homEquiv (x ≫ (D.uniqueUnderlyingIso E).hom) = D.representable.homEquiv x := by
  change E.representable.homEquiv
    (x ≫ E.representable.homEquiv.symm (D.representable.homEquiv (𝟙 D.abelian.scheme))) = _
  rw [E.representable.comp_homEquiv_symm, Equiv.apply_symm_apply,
    ← D.representable.homEquiv_comp, Category.comp_id]

theorem Data.DualAbelianData.uniqueUnderlyingIso_preserves_unit :
    η[D.abelian.scheme] ≫ (D.uniqueUnderlyingIso E).hom = η[E.abelian.scheme] := by
  apply E.representable.homEquiv.injective
  rw [D.uniqueUnderlyingIso_hom_classifies E]
  rw [MonObj.one_eq_one D.abelian.scheme, MonObj.one_eq_one E.abelian.scheme]
  exact (D.origin _).trans (E.origin _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual
