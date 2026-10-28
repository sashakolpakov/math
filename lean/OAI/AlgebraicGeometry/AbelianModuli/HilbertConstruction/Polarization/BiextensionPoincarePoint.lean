import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PoincareClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

/-! # Biextension Poincare Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BiextensionPoincarePoint

noncomputable section

/-! A fiber's polarization biextension is the Poincare point bundle classified by the pulled-back polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S T : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) (f : T ⟶ S)

theorem polarizationBiextension_poincarePoint_map :
    (Picard.PicardSheaf.familySchemeFunctor (A.pullback f).scheme).map ((Over.pullback f).map p) ≫
        (D.poincarePullbackOverMap f).left =
      (((Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme).left ≫ PolarizationData.poincareBaseChangeMap D f) := by
  rw [tensorHom_id, Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
  rfl

def polarizationBiextensionAt_poincareAtIso :
    ((D.pullback f).poincareAt ((Over.pullback f).map p)).sheaf ≅ (PolarizationData.polarizationBiextensionAt D p f).sheaf :=
  (Scheme.Modules.pullbackComp
    ((Picard.PicardSheaf.familySchemeFunctor (A.pullback f).scheme).map ((Over.pullback f).map p))
    (D.poincarePullbackOverMap f).left).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (polarizationBiextension_poincarePoint_map D p f)).app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BiextensionPoincarePoint
