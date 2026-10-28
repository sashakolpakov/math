import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.RankOneProjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.BasisSumFunctional

/-! # Basis Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisPoint.BundleCycles

noncomputable section

/-! A basis supplies a genuine section of the projective bundle
lying in every one of its basis charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem symmetricRankOne_basicOpen_top (R : Type) [CommRing R] :
    Proj.basicOpen (Grading.BundleCycles.symmetricGrading R R) (SymmetricAlgebra.ι R R 1) = ⊤ := by
  have h := BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap_opensRange (Module.Basis.singleton Unit R) ()
  rw [Module.Basis.singleton_apply] at h
  exact h.symm.trans (Scheme.Hom.opensRange_of_isIso _)

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Nonempty ι]
    (b : Module.Basis ι R M)

def symmetricBasisPoint : Spec (.of R) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  (RankOneProjective.BundleCycles.symmetricRankOneProjectiveIso R).inv ≫
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap (BasisSumFunctional.BundleCycles.basisSumFunctional b) (BasisSumFunctional.BundleCycles.basisSumFunctional_surjective b)

theorem symmetricBasisPoint_over :
    symmetricBasisPoint b ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M = 𝟙 _ := by
  unfold symmetricBasisPoint
  rw [Category.assoc, SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over]
  exact (RankOneProjective.BundleCycles.symmetricRankOneProjectiveIso R).inv_hom_id

theorem symmetricBasisPoint_preimage_basicOpen (i : ι) :
    symmetricBasisPoint b ⁻¹ᵁ Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i)) = ⊤ := by
  change ((RankOneProjective.BundleCycles.symmetricRankOneProjectiveIso R).inv ≫
    Proj.map (GradedMap.BundleCycles.symmetricGradedMap (BasisSumFunctional.BundleCycles.basisSumFunctional b)) _) ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage, Proj.map_preimage_basicOpen, GradedMap.BundleCycles.symmetricGradedMap_generator,
    BasisSumFunctional.BundleCycles.basisSumFunctional_basis, symmetricRankOne_basicOpen_top]
  rfl

theorem symmetricBasisPoint_mem_basicOpen (i : ι) (x : Spec (.of R)) :
    symmetricBasisPoint b x ∈ Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i)) := by
  change x ∈ symmetricBasisPoint b ⁻¹ᵁ Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i))
  rw [symmetricBasisPoint_preimage_basicOpen]
  trivial

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisPoint.BundleCycles
