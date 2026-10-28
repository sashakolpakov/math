import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueCycleFamily
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyReindex
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Residue Boundary Addition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueBoundaryAddition.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: addition laws for the complete geometric residue boundary

Summing the intrinsic finite family recovers exactly the explicit
geometric residue cycle. The pointwise product laws therefore imply
addition of the complete residue boundary in either rational function.
The proof covers all coefficients and all changes of finite support.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

def residueFamilySum : ({x : X // coheight x = 1} →₀ (X →₀ ℚ)) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.lsum ℚ (fun _ => LinearMap.id)

theorem residueFamilySum_eq_boundary (g h : X.functionFieldˣ) :
    residueFamilySum X (ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X hNormal g h) = Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h := by
  let i : Normal.PointResidue.BundleCycles.residueDivisorSupport X g h ↪ {x : X // coheight x = 1} :=
    ⟨fun x => ⟨x, Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight X g h x⟩,
      fun x y hxy => Subtype.ext (congrArg (fun z : {x : X // coheight x = 1} => (z : X)) hxy)⟩
  have hs : ((ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X hNormal g h).support : Set {x : X // coheight x = 1}) ⊆
      Set.range i := by
    intro x hx
    have hxD : (x : X) ∈ Normal.PointResidue.BundleCycles.residueDivisorSupport X g h := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hx) (ResidueCycleFamily.BundleCycles.normalResidueContribution_eq_zero X hNormal g h x hn)
    exact ⟨⟨x, hxD⟩, Subtype.ext rfl⟩
  exact Finite.FamilyReindex.BundleCycles.finiteFamily_sum_embedding i (ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X hNormal g h) hs

theorem normalResidueBoundaryCycle_mul_left (g h k : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal (g * h) k =
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g k + Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal h k := by
  have he := congrArg (residueFamilySum X) (ResidueCycleFamily.BundleCycles.normalResidueCycleFamily_mul_left X hNormal g h k)
  rw [map_add] at he
  exact (residueFamilySum_eq_boundary X hNormal (g * h) k).symm.trans
    (he.trans (congrArg₂ (· + ·) (residueFamilySum_eq_boundary X hNormal g k)
      (residueFamilySum_eq_boundary X hNormal h k)))

theorem normalResidueBoundaryCycle_mul_right (g h k : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g (h * k) =
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h + Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g k := by
  have he := congrArg (residueFamilySum X) (ResidueCycleFamily.BundleCycles.normalResidueCycleFamily_mul_right X hNormal g h k)
  rw [map_add] at he
  exact (residueFamilySum_eq_boundary X hNormal g (h * k)).symm.trans
    (he.trans (congrArg₂ (· + ·) (residueFamilySum_eq_boundary X hNormal g h)
      (residueFamilySum_eq_boundary X hNormal g k)))

end

/-!
# LineBundleCycles: alternating laws for the actual residue boundary

The unit quotient for two identical rational functions is one, so its
actual principal divisor is zero. Combining this with the proved global
product laws makes the complete residue boundary alternating. Inverting
one argument changes its sign.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem normalPointResidueFunction_self (x : X) (hx : coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (g : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx g g = 1 := by
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  let π := Classical.choose (IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x))
  have hπ : Irreducible π := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible _)
  have he : DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g g = 1 := by
    unfold DVRResidueOf.BundleCycles.dvrResidueQuotient DVRResidueOf.BundleCycles.dvrBalancedUnit
    simp
  exact (congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) he).trans (Geometric.ResidueLaws.BundleCycles.pointSupportResidueFunction_one X x)

variable (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

theorem normalResidueBoundaryCycle_self (g : X.functionFieldˣ) : Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g g = 0 := by
  have hf : ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X hNormal g g = 0 := by
    ext x y
    let := hNormal x
    change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (x : X))
      (Normal.PointResidue.BundleCycles.normalPointResidueFunction X x x.2 g g) y = 0
    rw [normalPointResidueFunction_self, Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_one]
    rfl
  exact (residueFamilySum_eq_boundary X hNormal g g).symm.trans
    ((congrArg (residueFamilySum X) hf).trans (map_zero (residueFamilySum X)))

theorem normalResidueBoundaryCycle_one_left (g : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal 1 g = 0 := by
  have he := normalResidueBoundaryCycle_mul_left X hNormal 1 1 g
  rw [one_mul] at he
  exact (add_left_cancel (a := Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal 1 g)
    ((add_zero _).trans he)).symm

theorem normalResidueBoundaryCycle_swap (g h : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h = -Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal h g := by
  have he := normalResidueBoundaryCycle_self X hNormal (g * h)
  rw [normalResidueBoundaryCycle_mul_left, normalResidueBoundaryCycle_mul_right,
    normalResidueBoundaryCycle_mul_right, normalResidueBoundaryCycle_self,
    normalResidueBoundaryCycle_self, zero_add, add_zero] at he
  exact eq_neg_iff_add_eq_zero.mpr he

theorem normalResidueBoundaryCycle_inv_left (g h : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g⁻¹ h = -Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h := by
  have he := normalResidueBoundaryCycle_mul_left X hNormal g g⁻¹ h
  rw [mul_inv_cancel, normalResidueBoundaryCycle_one_left] at he
  exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans he.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueBoundaryAddition.BundleCycles
