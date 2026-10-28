import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings

/-! # Abelian Integral -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.AbelianIntegral

noncomputable section

/-! Integrality of the actual abelian variety over its original field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

universe u

variable {k : Type u} [Field k] {g : ℕ}

theorem abelian_integral (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) : IsIntegral A.scheme.left :=
  AbelianScheme.HomExtensionLocalRings.LocalRings.integral_of_smooth_proper_connected A.scheme.hom

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.AbelianIntegral
