import OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearIsomorphisms
import Mathlib.RingTheory.Smooth.Basic

/-! # Square Zero Algebra Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.SquareZeroAlgebraComparison

noncomputable section

/-! Two formally smooth algebras with an identified reduction across
a square-zero base ideal have an actual algebra isomorphism lifting that
identification. This is an affine local deformation comparison. -/

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Algebra.FormallySmooth R S] [Algebra.FormallySmooth R T]

theorem exists_smooth_algebraEquiv_lift_squareZero (I : Ideal R) (hI : I * I = ⊥)
    (e : (S ⧸ I.map (algebraMap R S)) ≃ₐ[R] (T ⧸ I.map (algebraMap R T))) :
    ∃ f : S ≃ₐ[R] T,
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R T))).comp f.toAlgHom =
        e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))) := by
  let J := I.map (algebraMap R S)
  let K := I.map (algebraMap R T)
  let qS := Ideal.Quotient.mkₐ R J
  let qT := Ideal.Quotient.mkₐ R K
  have hJ : IsNilpotent J := by
    refine ⟨2, ?_⟩
    change (I.map (algebraMap R S)) ^ 2 = ⊥
    rw [pow_two, ← Ideal.map_mul, hI, Ideal.map_bot]
  have hK : IsNilpotent K := by
    refine ⟨2, ?_⟩
    change (I.map (algebraMap R T)) ^ 2 = ⊥
    rw [pow_two, ← Ideal.map_mul, hI, Ideal.map_bot]
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift K hK (e.toAlgHom.comp qS)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J hJ (e.symm.toAlgHom.comp qT)
  have hf' (s : S) : qT (f s) = e (qS s) := AlgHom.congr_fun hf s
  have hg' (t : T) : qS (g t) = e.symm (qT t) := AlgHom.congr_fun hg t
  have hS (s : S) : g (f s) - s ∈ I • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map]
    change g (f s) - s ∈ J
    apply (Ideal.Quotient.eq (I := J)).mp
    change qS (g (f s)) = qS s
    rw [hg', hf', e.symm_apply_apply]
  have hT (t : T) : f (g t) - t ∈ I • (⊤ : Submodule R T) := by
    rw [Ideal.smul_top_eq_map]
    change f (g t) - t ∈ K
    apply (Ideal.Quotient.eq (I := K)).mp
    change qT (f (g t)) = qT t
    rw [hf', hg', e.apply_symm_apply]
  exact ⟨AlgEquiv.ofBijective f
    (RepresentationTheory.Theta.Geometric.SquareZero.LinearIsomorphisms.linear_bijective_of_squareZero_inverse I hI f.toLinearMap g.toLinearMap hS hT), hf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.SquareZeroAlgebraComparison
