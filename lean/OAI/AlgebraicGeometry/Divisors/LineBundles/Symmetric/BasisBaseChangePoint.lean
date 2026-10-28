import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisBaseChangeCover
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisPoint

/-! # Basis Base Change Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisBaseChangePoint.BundleCycles

noncomputable section

/-! The actual section supplied by a basis remains inside every
base-changed basis chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι R M) {Y : Scheme.{0}} (g : Y ⟶ Spec (.of R))

def symmetricBasisBaseChangePoint : Y ⟶ pullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g :=
  pullback.lift (g ≫ BasisPoint.BundleCycles.symmetricBasisPoint b) (𝟙 Y) (by
    rw [Category.assoc, BasisPoint.BundleCycles.symmetricBasisPoint_over, Category.comp_id, Category.id_comp])

omit [Fintype ι] in
theorem symmetricBasisBaseChangePoint_fst :
    symmetricBasisBaseChangePoint b g ≫ pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g =
      g ≫ BasisPoint.BundleCycles.symmetricBasisPoint b := pullback.lift_fst _ _ _

omit [Fintype ι] in
theorem symmetricBasisBaseChangePoint_snd :
    symmetricBasisBaseChangePoint b g ≫ pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g =
      𝟙 Y := pullback.lift_snd _ _ _

theorem symmetricBasisBaseChangePoint_mem_chart (i : ι) (y : Y) :
    symmetricBasisBaseChangePoint b g y ∈ Set.range (BasisBaseChangeCover.BundleCycles.symmetricBasisBaseChangeChartMap b g i) := by
  apply (Set.ext_iff.mp (BasisBaseChangeCover.BundleCycles.symmetricBasisBaseChangeChart_range b g i) _).mpr
  have he : pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g (symmetricBasisBaseChangePoint b g y) =
      BasisPoint.BundleCycles.symmetricBasisPoint b (g y) := congrArg (fun k : Y ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M => k y)
        (symmetricBasisBaseChangePoint_fst b g)
  change pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g (symmetricBasisBaseChangePoint b g y) ∈
    (↑(Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i))) : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M))
  rw [he]
  exact BasisPoint.BundleCycles.symmetricBasisPoint_mem_basicOpen b i (g y)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisBaseChangePoint.BundleCycles
