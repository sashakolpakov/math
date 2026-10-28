import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DegreeOneCover
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Basis Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisCover.BundleCycles

noncomputable section

/-! The projective symmetric spectrum is covered by the actual
degree-one charts at any basis of its module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem symmetricIrrelevant_le_span_generators (b : ι → M)
    (hb : Submodule.span R (Set.range b) = ⊤) :
    (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading R M)).toIdeal ≤
      Ideal.span (Set.range (fun i => SymmetricAlgebra.ι R M (b i))) := by
  let I := Ideal.span (Set.range (fun i => SymmetricAlgebra.ι R M (b i)))
  have hM : ∀ m : M, SymmetricAlgebra.ι R M m ∈ I := by
    intro m
    have hm : m ∈ Submodule.span R (Set.range b) := by rw [hb]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      exact Ideal.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact I.zero_mem
    | add m n hm hn ihm ihn => rw [map_add]; exact I.add_mem ihm ihn
    | smul r m hm ih => rw [map_smul]; exact (I.restrictScalars R).smul_mem r ih
  rw [GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal]
  apply Ideal.span_le.mpr
  rintro s ⟨m, rfl⟩
  exact hM m

def symmetricBasisCover (b : Module.Basis ι R M) : (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (Grading.BundleCycles.symmetricGrading R M) (fun i => SymmetricAlgebra.ι R M (b i))
    (m := fun _ => 1) (fun i => DegreeOneCover.BundleCycles.symmetricGenerator_degree R M (b i)) (fun _ => by decide)
    (symmetricIrrelevant_le_span_generators b b.span_eq)

instance symmetricBasisCover_isOpenImmersion (b : Module.Basis ι R M) (i : ι) :
    IsOpenImmersion ((symmetricBasisCover b).f i) :=
  (symmetricBasisCover b).openCover.map_prop i

theorem symmetricBasisCover_opensRange (b : Module.Basis ι R M) (i : ι) :
    ((symmetricBasisCover b).f i).opensRange = Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i)) :=
  Proj.opensRange_awayι _ _ _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisCover.BundleCycles
