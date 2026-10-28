import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.NormalizedGraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberEulerGroundField

/-! # Graph Residue Fiber Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The graph-power Euler characteristic and section dimension on actual
residue fibers have the same type formula over every tame base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_residueFiberSections_normalized
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (m : ℕ) (hm : 0 < m) (x : S) :
    FiberEulerGroundField.lineBundleFieldSectionDimension (A.abelian.scheme.hom.fiberToSpecResidueField x)
      ((A.graphBundle.tensorPower m).pullback (A.abelian.scheme.hom.fiberι x)) =
        (2 : ℕ) ^ g * (∏ i, δ i) * m ^ g := by
  let b := S.fromSpecResidueField x
  let B := A.pullback b
  let f := A.abelian.scheme.hom.fiberι x
  let e : ((A.graphBundle.tensorPower m).pullback f).sheaf ≅ (B.graphBundle.tensorPower m).sheaf :=
    A.graphBundle.powerBaseChangeIso f m ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left m).mapIso (A.graphBundle_baseChangeIso b).symm
  exact (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso B.abelian.scheme.hom e).finrank_eq.trans
    (B.graphBundle_positivePower_sections_finrank_normalized hg hN
      (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit b) m hm)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_power_fiberEuler_normalized
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (m : ℕ) (x : S) :
    Geometric.FiberEuler.fiberEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m) x =
      ((2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ)) * (m : ℤ) ^ g := by
  let b := S.fromSpecResidueField x
  let B := A.pullback b
  let f := A.abelian.scheme.hom.fiberι x
  let e : ((A.graphBundle.tensorPower m).pullback f).sheaf ≅ (B.graphBundle.tensorPower m).sheaf :=
    A.graphBundle.powerBaseChangeIso f m ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left m).mapIso (A.graphBundle_baseChangeIso b).symm
  rw [FiberEulerGroundField.fiberEulerCharacteristic_eq_groundField]
  exact (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso B.abelian.scheme.hom e).trans
    (B.graphBundle_tensorPower_euler_normalized_overField hg hN
      (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit b) m)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
