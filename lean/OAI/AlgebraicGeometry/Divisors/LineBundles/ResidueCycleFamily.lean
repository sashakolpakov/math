import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws

/-! # Residue Cycle Family -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueCycleFamily.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the finitely supported family of actual residue divisors

The residue contribution vanishes outside the union of the two actual
principal-divisor supports: both orders are zero there. This yields a
finitely supported family on all codimension-one points. Its product
laws are proved pointwise from the actual rational-function and
principal-divisor laws, without choosing a common finite indexing set.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

def normalResidueContribution (g h : X.functionFieldˣ) (x : {x : X // coheight x = 1}) : X →₀ ℚ :=
  letI := hNormal x
  Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (x : X))
    (Normal.PointResidue.BundleCycles.normalPointResidueFunction X x x.2 g h)

theorem normalResidueContribution_mul_left (g h k : X.functionFieldˣ) (x : {x : X // coheight x = 1}) :
    normalResidueContribution X hNormal (g * h) k x =
      normalResidueContribution X hNormal g k x + normalResidueContribution X hNormal h k x := by
  let := hNormal x
  unfold normalResidueContribution
  rw [Geometric.ResidueLaws.BundleCycles.normalPointResidueFunction_mul_left]
  exact Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_mul _ _ _
    (Normal.PointResidue.BundleCycles.normalPointResidueFunction_ne_zero X x x.2 g k) (Normal.PointResidue.BundleCycles.normalPointResidueFunction_ne_zero X x x.2 h k)

theorem normalResidueContribution_mul_right (g h k : X.functionFieldˣ) (x : {x : X // coheight x = 1}) :
    normalResidueContribution X hNormal g (h * k) x =
      normalResidueContribution X hNormal g h x + normalResidueContribution X hNormal g k x := by
  let := hNormal x
  unfold normalResidueContribution
  rw [Geometric.ResidueLaws.BundleCycles.normalPointResidueFunction_mul_right]
  exact Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_mul _ _ _
    (Normal.PointResidue.BundleCycles.normalPointResidueFunction_ne_zero X x x.2 g h) (Normal.PointResidue.BundleCycles.normalPointResidueFunction_ne_zero X x x.2 g k)

theorem normalResidueContribution_eq_zero (g h : X.functionFieldˣ) (x : {x : X // coheight x = 1})
    (hx : (x : X) ∉ Normal.PointResidue.BundleCycles.residueDivisorSupport X g h) : normalResidueContribution X hNormal g h x = 0 := by
  classical
  let := hNormal x
  have hg : X.ord (g : X.functionField) x = 0 := by
    change Ord.BundleCycles.principalDivisor X (g : X.functionField) x = 0
    apply Finsupp.notMem_support_iff.mp
    exact fun hm => hx (Finset.mem_union_left _ hm)
  have hh : X.ord (h : X.functionField) x = 0 := by
    change Ord.BundleCycles.principalDivisor X (h : X.functionField) x = 0
    apply Finsupp.notMem_support_iff.mp
    exact fun hm => hx (Finset.mem_union_right _ hm)
  unfold normalResidueContribution
  rw [Geometric.ResidueLaws.BundleCycles.normalPointResidueFunction_zero_orders X x x.2 g h hg hh, Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_one]

theorem normalResidueContribution_finite (g h : X.functionFieldˣ) :
    {x : {x : X // coheight x = 1} | normalResidueContribution X hNormal g h x ≠ 0}.Finite := by
  have hs : {x : {x : X // coheight x = 1} | (x : X) ∈ Normal.PointResidue.BundleCycles.residueDivisorSupport X g h}.Finite :=
    (Normal.PointResidue.BundleCycles.residueDivisorSupport X g h).finite_toSet.preimage Subtype.val_injective.injOn
  apply hs.subset
  intro x hx
  by_contra hn
  exact hx (normalResidueContribution_eq_zero X hNormal g h x hn)

/-- The actual finitely supported family of residue divisors at codimension-one points. -/
def normalResidueCycleFamily (g h : X.functionFieldˣ) : {x : X // coheight x = 1} →₀ (X →₀ ℚ) :=
  Finsupp.ofSupportFinite (normalResidueContribution X hNormal g h)
    (normalResidueContribution_finite X hNormal g h)

theorem normalResidueCycleFamily_mul_left (g h k : X.functionFieldˣ) :
    normalResidueCycleFamily X hNormal (g * h) k =
      normalResidueCycleFamily X hNormal g k + normalResidueCycleFamily X hNormal h k := by
  ext x y
  exact congrArg (fun z : X →₀ ℚ => z y) (normalResidueContribution_mul_left X hNormal g h k x)

theorem normalResidueCycleFamily_mul_right (g h k : X.functionFieldˣ) :
    normalResidueCycleFamily X hNormal g (h * k) =
      normalResidueCycleFamily X hNormal g h + normalResidueCycleFamily X hNormal g k := by
  ext x y
  exact congrArg (fun z : X →₀ ℚ => z y) (normalResidueContribution_mul_right X hNormal g h k x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueCycleFamily.BundleCycles
