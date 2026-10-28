import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseCohomologyModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CohomologyEulerComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResiduePrime

/-! # Fiber Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiberEuler

noncomputable section

/-! The Euler characteristic of genuine geometric fiber cohomology equals the alternating rank function of a finite projective cohomology model. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def fiberEulerCharacteristic {X S : Scheme.{u}} (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (x : S) : ℤ :=
  ∑ᶠ q : ℕ, (-1 : ℤ) ^ q *
    (Module.finrank Γ(Spec (S.residueField x), ⊤)
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom q).obj
        (L.pullback (f.fiberι x)).sheaf) : ℤ)

theorem fiberEulerCharacteristic_eq_modelEuler
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (x : S)
    (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite Γ(S, ⊤) (D.X q))
    (hprojective : ∀ q, Module.Projective Γ(S, ⊤) (D.X q))
    (hbound : ∀ q, N ≤ q → IsZero (D.X q))
    (he : ∀ q, Nonempty
      ((((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
        (.up ℕ)).obj D).homology q ≅
          (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom q).obj
            (L.pullback (f.fiberι x)).sheaf)) :
    fiberEulerCharacteristic f L x = HilbertConstruction.Finite.ProjectiveEulerFunction.finiteProjectiveEulerAt D (N + 1) (S.toSpecΓ x) := by
  let : Field Γ(Spec (S.residueField x), ⊤) :=
    ((Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField (S.residueField x))).toField
  let g := S.fromSpecResidueField x
  let C := ((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex (.up ℕ)).obj D
  have hs : fiberEulerCharacteristic f L x =
      ∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q *
        (Module.finrank Γ(Spec (S.residueField x), ⊤)
          ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom q).obj
            (L.pullback (f.fiberι x)).sheaf) : ℤ) := by
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hnot
    have hn : N ≤ q := by
      simp only [Finset.mem_coe, Finset.mem_range] at hnot
      omega
    have hz : IsZero (C.X q) := (ModuleCat.extendScalars g.appTop.hom).map_isZero (hbound q hn)
    have hH := (he q).some.isZero_iff.mp (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology
    have := ModuleCat.isZero_iff_subsingleton.mp hH
    exact hq (by simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero])
  have ht := HilbertConstruction.Field.CohomologyEulerComparison.finiteProjectiveEulerAt_fieldHomology_sum g.appTop.hom D N hfinite hprojective
    (hbound (N + 1) (by omega))
  rw [Affine.ResiduePrime.residuePoint_prime_comap S x] at ht
  refine hs.trans (Eq.trans ?_ ht.symm)
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ)) (he q).some.toLinearEquiv.finrank_eq.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiberEuler
