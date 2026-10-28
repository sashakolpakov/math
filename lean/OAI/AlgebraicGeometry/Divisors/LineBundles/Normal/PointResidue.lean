import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueRegular
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field

/-! # Point Residue -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: residue functions at normal codimension-one points

An integrally closed codimension-one local ring on an integral Noetherian
scheme is a DVR. The local-ring dimension and non-field conditions are
proved from the actual point's coheight. A uniformizer can then be chosen
to construct the already proved, choice-independent geometric residue
function. This is the local normality criterion used on normalization.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]

include hx

theorem normal_stalk_isDVR : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  let : Ring.DimensionLEOne R := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let : IsDedekindDomain R :=
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }
  have hn : ¬ IsField R := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    change ringKrullDim (X.presheaf.stalk x) = 0 at hzero
    rw [ringKrullDim_stalk_eq_coheight, hx] at hzero
    exact (by decide : (1 : WithBot ℕ∞) ≠ 0) hzero
  have ht : IsDiscreteValuationRing R ↔ IsDedekindDomain R :=
    (IsDiscreteValuationRing.TFAE R hn).out 1 3
  exact ht.mpr inferInstance

def normalPointResidueFunction (g h : X.functionFieldˣ) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField :=
  letI := normal_stalk_isDVR X x hx
  let π := Classical.choose (IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x))
  Geometric.ResidueFunction.BundleCycles.geometricResidueFunction X x π (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible _)) g h

theorem normalPointResidueFunction_ne_zero (g h : X.functionFieldˣ) :
    normalPointResidueFunction X x hx g h ≠ 0 := by
  let := normal_stalk_isDVR X x hx
  exact Geometric.ResidueFunction.BundleCycles.geometricResidueFunction_ne_zero X x _ _ g h

theorem normalPointResidueFunction_eq (π : X.presheaf.stalk x) (hπ : Irreducible π)
    (g h : X.functionFieldˣ) :
    letI := normal_stalk_isDVR X x hx
    normalPointResidueFunction X x hx g h = Geometric.ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g h := by
  let := normal_stalk_isDVR X x hx
  exact Geometric.ResidueFunction.BundleCycles.geometricResidueFunction_independent X x _ _ π hπ g h

end

/-!
# LineBundleCycles: the finite geometric residue boundary on a normal scheme

The union of the two actual principal-divisor supports is finite and
consists of codimension-one points. Local integral closure supplies the
nonzero rational residue function on each reduced support. Their actual
principal divisors form a finite cycle, with complete grading recovery
and zero Chow class. The further equality with the iterated intersection
boundary requires reciprocity and is not asserted here.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem principalDivisor_support_coheight (g : X.functionField) (x : X)
    (hx : x ∈ (Ord.BundleCycles.principalDivisor X g).support) : coheight x = 1 := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hx) (Scheme.ord_eq_zero_of_coheight_neq_one h g)

def residueDivisorSupport (g h : X.functionFieldˣ) : Finset X := by
  classical
  exact (Ord.BundleCycles.principalDivisor X (g : X.functionField)).support ∪ (Ord.BundleCycles.principalDivisor X (h : X.functionField)).support

theorem residueDivisorSupport_coheight (g h : X.functionFieldˣ) (x : residueDivisorSupport X g h) :
    coheight (x : X) = 1 := by
  classical
  rcases Finset.mem_union.mp x.2 with hx | hx
  · exact principalDivisor_support_coheight X (g : X.functionField) x hx
  · exact principalDivisor_support_coheight X (h : X.functionField) x hx

variable (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

def normalResidueFunctionOnSupport (g h : X.functionFieldˣ) (x : residueDivisorSupport X g h) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (x : X))).functionField :=
  letI := hNormal x
  normalPointResidueFunction X x (residueDivisorSupport_coheight X g h x) g h

theorem normalResidueFunctionOnSupport_ne_zero (g h : X.functionFieldˣ)
    (x : residueDivisorSupport X g h) : normalResidueFunctionOnSupport X hNormal g h x ≠ 0 := by
  let := hNormal x
  exact normalPointResidueFunction_ne_zero X x (residueDivisorSupport_coheight X g h x) g h

/-- The actual finite sum of principal divisors of the residue functions. -/
def normalResidueBoundaryCycle (g h : X.functionFieldˣ) : X →₀ ℚ :=
  ∑ x : residueDivisorSupport X g h,
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (x : X))
      (normalResidueFunctionOnSupport X hNormal g h x)

variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

def normalGradedResidueBoundaryCycle (d : ℕ) (g h : X.functionFieldˣ) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ :=
  ∑ x : residueDivisorSupport X g h,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (irreducibleSetEquivPoints.symm (x : X))
      (normalResidueFunctionOnSupport X hNormal g h x)

variable [LocallyOfFiniteType f]

theorem normalResidueSupport_dimension (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)
    (g h : X.functionFieldˣ) (x : residueDivisorSupport X g h) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (x : X)) f = d + 1 := by
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one f x (residueDivisorSupport_coheight X g h x)
  omega

theorem normalGradedResidueBoundaryCycle_push (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)
    (g h : X.functionFieldˣ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (normalGradedResidueBoundaryCycle X hNormal f d g h) =
      normalResidueBoundaryCycle X hNormal g h := by
  unfold normalGradedResidueBoundaryCycle normalResidueBoundaryCycle
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d _ (normalResidueSupport_dimension X f d hX g h x) _

/-- Every summand is a constructed principal divisor of the correct dimension. -/
theorem normalGradedResidueBoundaryCycle_chow_zero (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)
    (g h : X.functionFieldˣ) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (normalGradedResidueBoundaryCycle X hNormal f d g h) = 0 := by
  unfold normalGradedResidueBoundaryCycle
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro x _
  exact DimensionChow.BundleCycles.dimensionCycleToChowQ_principal f d _ (normalResidueSupport_dimension X f d hX g h x) _
    (normalResidueFunctionOnSupport_ne_zero X hNormal g h x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue.BundleCycles
