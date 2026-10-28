import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSingleRowTotal

/-! # Row Total Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalCoordinates

noncomputable section

/-! The abelian single-row coordinates specialize to the original
module-valued coordinates, including their literal degree shift. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {R : Type u} [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.X p).X q))

theorem restrictionIso_eq :
    AbelianSingleRowTotal.restrictionIso B c hB = RowTotal.restrictionIso B c hB := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext p
  rfl

theorem homologyIso_eq (n : ℕ) :
    AbelianSingleRowTotal.homologyIso B c hB n = RowTotal.homologyIso B c hB n := by
  unfold AbelianSingleRowTotal.homologyIso
  rw [restrictionIso_eq]
  apply Iso.ext
  simp only [RowTotal.homologyIso, RowTotalNaturality.supportedIso,
    Iso.trans_hom, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalCoordinates
