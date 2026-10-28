import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType

/-! # Proper -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper.BundleCycles

noncomputable section

/-! The projective spectrum of a finite module's actual symmetric
algebra is proper over the base ring. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem symmetricAlgebra_finiteType : Algebra.FiniteType R (SymmetricAlgebra R M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let T := Algebra.adjoin R (SymmetricAlgebra.ι R M '' (s : Set M))
  have hi : ∀ m, SymmetricAlgebra.ι R M m ∈ T := by
    intro m
    have hm : m ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact T.zero_mem
    | add x y hx hy ihx ihy => rw [map_add]; exact T.add_mem ihx ihy
    | smul r x hx ih => rw [map_smul]; exact T.smul_mem ih r
  have hT : T = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => exact T.algebraMap_mem r
    | ι m => exact hi m
    | mul a b ha hb => exact T.mul_mem ha hb
    | add a b ha hb => exact T.add_mem ha hb
  refine ⟨s.image (SymmetricAlgebra.ι R M), ?_⟩
  rw [Finset.coe_image]
  exact hT

theorem symmetricDegreeZero_finiteType :
    Algebra.FiniteType (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) (SymmetricAlgebra R M) := by
  let := symmetricAlgebra_finiteType R M
  let : IsScalarTower R (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) (SymmetricAlgebra R M) := by
    constructor
    intro r s a
    change (r • s.val) * a = r • (s.val * a)
    exact smul_mul_assoc r s.val a
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) (SymmetricAlgebra R M)

instance symmetricProjectiveToBase_isProper : IsProper (Scheme.BundleCycles.symmetricProjectiveToBase R M) := by
  let := symmetricDegreeZero_finiteType R M
  let e := (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom) := e.isIso_hom
  unfold Scheme.BundleCycles.symmetricProjectiveToBase
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper.BundleCycles
