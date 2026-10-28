import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleCotangentCriterion
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.RingHom.Etale

/-! # Differential Coordinates Etale -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialCoordinatesEtale

noncomputable section

/-! Functions whose differentials form a basis on a finitely presented formally smooth algebra define an actual etale map from the polynomial algebra in those functions. -/
open _root_.Algebra TensorProduct
open scoped TensorProduct
universe u v w

theorem etale_aeval_of_basis_differentials
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [FormallySmooth R S] [FinitePresentation R S]
    {ι : Type w} [Finite ι] (x : ι → S) (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R S (x i)) :
    (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] S).toRingHom.Etale := by
  let A := MvPolynomial ι R
  let φ : A →ₐ[R] S := MvPolynomial.aeval x
  let : Algebra A S := φ.toAlgebra
  have : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let B : Module.Basis ι S (S ⊗[A] Ω[A⁄R]) := (KaehlerDifferential.mvPolynomialBasis R ι).baseChange S
  let e : (S ⊗[A] Ω[A⁄R]) ≃ₗ[S] Ω[S⁄R] := B.equiv b (Equiv.refl ι)
  have he : KaehlerDifferential.mapBaseChange R A S = e.toLinearMap := by
    apply B.ext
    intro i
    change KaehlerDifferential.mapBaseChange R A S (B i) = e (B i)
    rw [show e (B i) = b i by
      simp only [e, Module.Basis.equiv_apply, Equiv.refl_apply]]
    dsimp only [B]
    rw [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
    change KaehlerDifferential.D R S ((MvPolynomial.aeval x) (MvPolynomial.X i)) = b i
    rw [MvPolynomial.aeval_X]
    exact (hb i).symm
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R A S) := by
    rw [he]
    exact e.bijective
  have hzero (z : Ω[S⁄A]) : z = 0 := by
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R A S z
    obtain ⟨w, rfl⟩ := hbij.surjective y
    exact (KaehlerDifferential.exact_mapBaseChange_map R A S).apply_apply_eq_zero w
  have : FormallyUnramified A S := ⟨⟨fun x y => (hzero x).trans (hzero y).symm⟩⟩
  have : FormallyEtale A S := EtaleCotangentCriterion.formallyEtale_of_cotangent_injective R A S hbij.injective
  have : FinitePresentation A S := FinitePresentation.of_restrict_scalars_finitePresentation R A S
  change Etale A S
  exact { formallyEtale := inferInstance, finitePresentation := inferInstance }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialCoordinatesEtale
