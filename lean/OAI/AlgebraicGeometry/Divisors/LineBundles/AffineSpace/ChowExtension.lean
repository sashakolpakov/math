import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleGrading

/-! # Chow Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowExtension.BundleCycles

noncomputable section

/-! # LineBundleCycles: the canonical affine-space Chow map is the quotient of actual fiber-generic extension -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (ι : Type) [Finite ι]

theorem affineSpaceChowEquiv_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι)
        (CycleGrading.BundleCycles.affineSpaceGradedCycleExtension X f ι d z) := by
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv_pointClass,
    ← CycleGrading.BundleCycles.affineSpaceGradedCycleExtension_forget, Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion]

theorem affineSpaceGradedCycleExtension_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι)).comap
        (CycleGrading.BundleCycles.affineSpaceGradedCycleExtension X f ι d) := by
  intro z hz
  change CycleGrading.BundleCycles.affineSpaceGradedCycleExtension X f ι d z ∈
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι)
  apply (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff _ _ _).mp
  rw [← affineSpaceChowEquiv_cycle, (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff f d z).mpr hz, map_zero]

def affineSpaceChowExtension (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι) :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ
    (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι))
    (CycleGrading.BundleCycles.affineSpaceGradedCycleExtension X f ι d) (affineSpaceGradedCycleExtension_relations X f ι d)

theorem affineSpaceChowExtension_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    affineSpaceChowExtension X f ι d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι)
        (CycleGrading.BundleCycles.affineSpaceGradedCycleExtension X f ι d z) := rfl

theorem affineSpaceChowExtension_eq_equiv (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    affineSpaceChowExtension X f ι d a = FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [affineSpaceChowExtension_cycle, affineSpaceChowEquiv_cycle]

theorem affineSpaceChowExtension_bijective (d : ℕ) :
    Function.Bijective (affineSpaceChowExtension X f ι d) := by
  have h : (affineSpaceChowExtension X f ι d : DimensionChow.BundleCycles.DimensionChowQ f d →
      DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι)) = FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d :=
    funext (affineSpaceChowExtension_eq_equiv X f ι d)
  rw [h]
  exact (FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).bijective

def affineSpaceChowPullbackEquiv (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι) :=
  LinearEquiv.ofBijective (affineSpaceChowExtension X f ι d)
    (affineSpaceChowExtension_bijective X f ι d)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowExtension.BundleCycles
