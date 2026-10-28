import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryReducedPointCount
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Splitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Ordinary Field Extension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFieldExtension.Construction

noncomputable section

/-! Ordinary q-rank is preserved after every field extension, by the
original full torsion splitting evaluated on the extension-field test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k F : Type} [Field k] [IsAlgClosed k] [Field F]
  {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (q : ℕ) [Fact q.Prime] [CharP k q]

theorem ordinary_torsionCard_fieldExtension
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (f : Spec (.of F) ⟶ Spec (.of k)) :
    Nat.card ((A.abelian.pullback f).torsionPoints q (Over.mk (𝟙 (Spec (.of F))))) = q ^ g := by
  obtain ⟨e⟩ := HodgeConjecture.HeckeCycles.Ordinary.Splitting.CM.splitting A q hordinary 1
  exact OrdinaryReducedPointCount.Construction.splitTorsion_torsionCard_fieldExtension A.abelian q e f

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFieldExtension.Construction
