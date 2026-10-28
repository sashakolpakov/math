import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactProductNormalization
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

/-! # Compact Product Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactProductTrace.Constructions

noncomputable section

/-!
# DegreeTwo: integration of the actual compact exterior cup in coordinate spaces

Both inputs range over all actual compactly supported top cohomology.
The output is integrated after the specified genuine complex-linear coordinates.
The coefficient is the previously computed nonzero local cup coefficient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

set_option backward.isDefEq.respectTransparency false

theorem moduleIso_inverse_comp_hom_apply {M N P : ModuleCat.{0} ℚ}
    (e : M ≅ N) (f : M ⟶ P) (a : M) : (e.inv ≫ f) (e.hom a) = f a := by
  change f (e.inv (e.hom a)) = f a
  rw [Iso.hom_inv_id_apply]

def compactExteriorTopProduct (d c : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2*d))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin c → ℂ)) (2*c)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) (2*(d+c)) :=
  eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ)))) (Nat.mul_add 2 d c).symm)
    (CompactExteriorCup.Constructions.compactExteriorCup (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) (2*d) (2*c) a b)

def compactProductCoordinateTrace (d c : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) (2*(d+c)) ⟶ ModuleCat.of ℚ ℚ :=
  (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
    (LocalProductCoefficient.Constructions.productFlattenCoordinates d c).toHomeomorph (2*(d+c))).inv ≫
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace (d+c) (M := Fin (d+c) → ℂ)

theorem compactProductCoordinateTrace_point (d c : ℕ) :
    compactProductCoordinateTrace d c (CompactProductNormalization.Constructions.compactProductPointTop d c) =
      LocalProductCoefficient.Constructions.localProductCupCoefficient d c := by
  rw [CompactProductNormalization.Constructions.compactProductPointTop_normalization, map_smul]
  unfold compactProductCoordinateTrace
  rw [moduleIso_inverse_comp_hom_apply, AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_coordinate]
  change LocalProductCoefficient.Constructions.localProductCupCoefficient d c *
    AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv (d+c) (CompactPointNormalization.Constructions.compactPointDualClass (d+c)) = _
  rw [CompactPointNormalization.Constructions.compactPointDualClass_normalization, mul_one]

theorem compactExteriorTopProduct_eq_smul (d c : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2*d))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin c → ℂ)) (2*c)) :
    compactExteriorTopProduct d c a b =
      (AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d a *
        AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv c b) • CompactProductNormalization.Constructions.compactProductPointTop d c := by
  conv_lhs => rw [CompactPointNormalization.Constructions.compactTopClass_eq_smul_point d a, CompactPointNormalization.Constructions.compactTopClass_eq_smul_point c b]
  simp only [compactExteriorTopProduct, map_smul, LinearMap.smul_apply,
    CompactProductNormalization.Constructions.compactProductPointTop, mul_smul]
  exact smul_comm _ _ _

theorem compactExteriorTopProduct_trace (d c : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2*d))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin c → ℂ)) (2*c)) :
    compactProductCoordinateTrace d c (compactExteriorTopProduct d c a b) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := Fin d → ℂ) a *
        AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace c (M := Fin c → ℂ) b * LocalProductCoefficient.Constructions.localProductCupCoefficient d c := by
  rw [compactExteriorTopProduct_eq_smul, map_smul, compactProductCoordinateTrace_point,
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_coordinate, AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_coordinate]
  rfl

theorem compactExteriorTopProduct_ne_zero (d c : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2*d))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin c → ℂ)) (2*c))
    (ha : a ≠ 0) (hb : b ≠ 0) : compactExteriorTopProduct d c a b ≠ 0 := by
  rw [compactExteriorTopProduct_eq_smul]
  apply smul_ne_zero _ (CompactProductNormalization.Constructions.compactProductPointTop_ne_zero d c)
  apply mul_ne_zero
  · intro h
    exact ha ((AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d).injective
      (h.trans (map_zero _).symm))
  · intro h
    exact hb ((AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv c).injective
      (h.trans (map_zero _).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactProductTrace.Constructions
