import OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentTo
import OAI.NumberTheory.Quaternion.Arithmetic.ProductLieIdeals

/-! # Product Tangent Lie -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentLie

noncomputable section

/-! The simultaneous tangent span is a Lie subalgebra, and a
commensurated tangent subalgebra with nonzero simple-factor projections
equals the full local tangent algebra. -/

open scoped Classical _root_.NumberField OAI.NumberTheory.Quaternion.Arithmetic.ProductLieIdeals.LieProducts
open IsDedekindDomain Set

attribute [local instance] LieRing.ofAssociativeRing

variable {F κ : Type} [Field F] [NumberField F] [Field κ] {n : ℕ} {ι : Type*}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F))
variable [∀ i, Algebra κ ((v i).adicCompletion F)]

theorem product_tangentSpan_preserved_by_member
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))
    (hg : g ∈ H) :
    MapsTo (ProductTangentTo.productMatrixConjugation (κ := κ) G v g)
      (Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1) : Set _)
      (Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1) : Set _) := by
  have he : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg)
  have ht := ProductTangentTo.productMatrixConjugation_mapsTo_tangentCone (κ := κ) G v H g
  rw [he] at ht
  let W := Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1)
  have hle : W ≤ W.comap (ProductTangentTo.productMatrixConjugation (κ := κ) G v g).toLinearMap := by
    apply Submodule.span_le.mpr
    exact fun x hx => Submodule.subset_span (ht hx)
  exact hle

def productMatrixTangentLie
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hclosed : IsClosed (Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (H : Set _)) 1) : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))) :
    LieSubalgebra κ (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) :=
  { Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1) with
    lie_mem' := by
      intro X Y hX hY
      change X * Y - Y * X ∈ Submodule.span κ
        (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1)
      exact ProductTangentTo.product_tangentSpan_commutator_mem (κ := κ) G v H _ hclosed
        (product_tangentSpan_preserved_by_member (κ := κ) G v H) hY hX }

theorem product_tangentSpan_eq_of_simple_factors [Fintype ι]
    (B : ∀ i, LieSubalgebra κ (Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
    [∀ i, LieAlgebra.IsSimple κ (B i)]
    (H R : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hcomm : ∀ g ∈ R, (H.map (MulAut.conj g).toMonoidHom).Commensurable H)
    (hclosed : IsClosed (Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (H.topologicalClosure : Set _)) 1) : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))))
    (hfull : Submodule.span κ (tangentConeAt κ (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1) =
      Submodule.pi univ (fun i => (B i).toSubmodule))
    (hR : Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (R.topologicalClosure : Set _)) 1) =
      Submodule.span κ (tangentConeAt κ (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1))
    (hproj : ∀ i, ∃ X ∈ Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (H.topologicalClosure : Set _)) 1), X i ≠ 0) :
    Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H.topologicalClosure : Set _)) 1) =
      Submodule.span κ (tangentConeAt κ (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1) := by
  let J := productMatrixTangentLie (κ := κ) G v H.topologicalClosure hclosed
  have hJB : J ≤ ProductLieIdeals.piLieSubalgebra B := by
    intro X hX
    apply hfull.le
    apply (Submodule.span_mono (tangentConeAt_mono (image_subset_range _ _)))
    exact hX
  have he : J = ProductLieIdeals.piLieSubalgebra B := by
    apply ProductLieIdeals.pi_invariant_subalgebra_eq B J hJB _ hproj
    intro X Y hX hY
    change X * Y - Y * X ∈ Submodule.span κ
      (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H.topologicalClosure : Set _)) 1)
    apply ProductTangentTo.product_tangent_commutator_mem_of_commensurated (κ := κ) G v H R hcomm hclosed hY
    exact hR.symm.le (hfull.symm.le hX)
  have hs := congrArg LieSubalgebra.toSubmodule he
  exact hs.trans hfull.symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentLie
