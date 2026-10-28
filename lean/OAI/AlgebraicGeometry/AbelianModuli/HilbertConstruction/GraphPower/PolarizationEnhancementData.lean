import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes

/-! # Polarization Enhancement Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData

noncomputable section

/-! The concrete dual, polarization, and power-line comparison on a
full-level abelian family. Uniqueness of their moduli class is proved separately. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

structure GraphPowerPolarizationEnhancement {S : Scheme.{u}} {g N : ℕ}
    (δ : Fin g → ℕ) (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ) where
  dual : Dual.Data.DualAbelianData F.abelian
  polarization : PolarizationData.Polarization dual δ
  powerIso : Nonempty (L.sheaf ≅ ((PoincareGraph.Bundles.poincareGraphBundle dual polarization.isogeny.hom).tensorPower d).sheaf)

namespace GraphPowerPolarizationEnhancement
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ} {F : Level.Data.AbelianSchemeWithFullLevel g N S}
variable {L : Line.Bundles.LineBundle F.abelian.scheme.left} {d : ℕ}

def object (D : GraphPowerPolarizationEnhancement δ F L d) : PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := F.abelian
  dual := D.dual
  polarization := D.polarization
  level := F.level

end GraphPowerPolarizationEnhancement

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData
