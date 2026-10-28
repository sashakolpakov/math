import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartGauges
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorGaugeNaturality

/-! # Gauged Algebra Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GaugedAlgebraSquare

noncomputable section

/-! Correcting both sides of an actual product-chart restriction
square preserves that square when the correction derivations restrict. -/

open scoped TensorProduct

variable {k A B P Q : Type*} [CommRing k] [CommRing A] [CommRing B]
    [CommRing P] [CommRing Q] [Algebra k A] [Algebra k B]
    [Algebra (DualNumber k) P] [Algebra (DualNumber k) Q]

theorem gaugeDualProductChart_square
    (f : P ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (g : Q ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (r : P →ₐ[DualNumber k] Q) (q : A →ₐ[k] B)
    (d : Derivation k A A) (e : Derivation k B B)
    (h : g.toAlgHom.comp r =
      (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q).comp f.toAlgHom)
    (hde : ∀ a, q (d a) = e (q a)) :
    (Smooth.DualChartGauges.gaugeDualProductChart g e).toAlgHom.comp r =
      (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q).comp
        (Smooth.DualChartGauges.gaugeDualProductChart f d).toAlgHom := by
  apply AlgHom.ext
  intro p
  change Dual.TensorDerivationGauges.dualTensorDerivationGauge e (g (r p)) =
    Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q
      (Dual.TensorDerivationGauges.dualTensorDerivationGauge d (f p))
  have hp := AlgHom.congr_fun h p
  change g (r p) = Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q (f p) at hp
  rw [hp]
  exact (AlgHom.congr_fun (Dual.TensorGaugeNaturality.dualTensorDerivationGauge_natural q d e hde) (f p)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GaugedAlgebraSquare
