import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections

/-! # Finite Coproducts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.FiniteCoproducts

noncomputable section

/-! Finite coproducts of quasicoherent finite-type sheaves remain quasicoherent and finite type. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem module_finiteType_finite_coproduct {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (M : ι → X.Modules) (hMq : ∀ i, (M i).IsQuasicoherent) (hMt : ∀ i, (M i).IsFiniteType) :
    (∐ M).IsFiniteType := by
  have : (∐ M).IsQuasicoherent := Coproducts.module_quasicoherent_coproduct M hMq
  apply HilbertConstruction.Finite.TypeFromAffineSections.module_finiteType_of_affine_sections_finite
  intro U
  apply HilbertConstruction.Finite.CoproductSections.finite_coproduct_sections M U.1
  intro i
  have : (M i).IsQuasicoherent := hMq i
  have : (M i).IsFiniteType := hMt i
  exact Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite (M i) U

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.FiniteCoproducts
