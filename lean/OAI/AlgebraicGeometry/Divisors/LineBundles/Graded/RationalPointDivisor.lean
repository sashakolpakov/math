import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Rational Point Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.RationalPointDivisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the complete rational divisor of an integral scheme in its actual dimension grade
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

def gradedRationalPointDivisor (d : ℕ) (g : X.functionField) : GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ :=
  Finsupp.comapDomain (GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)
    (GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective.injOn

theorem gradedRationalPointDivisor_push [LocallyOfFiniteType f] (d : ℕ)
    (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) (g : X.functionField) :
    GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (gradedRationalPointDivisor X f d g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g := by
  have hs : ((RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g).support : Set X) ⊆
      Set.range (GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) := by
    intro x hx
    have hne : X.ord g x ≠ 0 := by
      intro hz
      exact (Finsupp.mem_support_iff.mp hx) ((RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply X g x).trans
        ((congrArg (fun n : ℤ => (n : ℚ)) hz).trans Int.cast_zero))
    have hc : coheight x = 1 := by
      by_contra hn
      exact hne (Scheme.ord_eq_zero_of_coheight_neq_one hn g)
    refine ⟨⟨x, ?_⟩, rfl⟩
    have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one f x hc
    omega
  exact (Finsupp.embDomain_eq_mapDomain (GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d)
    (gradedRationalPointDivisor X f d g)).symm.trans (Finsupp.embDomain_comapDomain hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.RationalPointDivisor.BundleCycles
