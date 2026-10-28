import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BiextensionPoincarePoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Polarization Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PolarizationFormula.PolarizedAbelianWithLevel

noncomputable section

/-! Geometric positivity supplies the normalized Poincare formula on each
geometric fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem geometricPullback_normalizedPolarizationFormula
    (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S) :
    let B := A.pullback f
    ∃ L : Line.Bundles.LineBundle B.abelian.scheme.left,
      Nonempty ((((B.dual.poincareAt B.polarization.isogeny.hom).tensor
        (L.pullback (fst B.abelian.scheme B.abelian.scheme).left)).tensor
          (L.pullback (snd B.abelian.scheme B.abelian.scheme).left)).sheaf ≅
        (L.pullback μ[B.abelian.scheme].left).sheaf) := by
  let B := A.pullback f
  obtain ⟨L, _, _, ⟨e⟩⟩ := A.polarization.positive K f
  let L₁ := L.pullback (fst B.abelian.scheme B.abelian.scheme).left
  let L₂ := L.pullback (snd B.abelian.scheme B.abelian.scheme).left
  exact ⟨L, ⟨Tensor.Bifunctor.tensorModuleMapIso (Tensor.Bifunctor.tensorModuleMapIso
    (Polarization.BiextensionPoincarePoint.polarizationBiextensionAt_poincareAtIso A.dual A.polarization.isogeny.hom f)
      (Iso.refl L₁.sheaf)) (Iso.refl L₂.sheaf) ≪≫ e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PolarizationFormula.PolarizedAbelianWithLevel
