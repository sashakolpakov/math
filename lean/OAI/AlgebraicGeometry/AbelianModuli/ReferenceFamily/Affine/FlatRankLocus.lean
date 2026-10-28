import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FlatModuleRankOpen
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientPoints
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Flat Rank Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.FlatRankLocus

noncomputable section

/-! The clopen rank locus of a finite projective module over the global
functions of an affine scheme classifies all test schemes using their
actual scheme-point coefficient homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem exists_affine_flat_module_rank_locus (X : Scheme.{0}) [IsAffine X]
    (V : Type) [AddCommGroup V] [Module Γ(X, ⊤) V]
    [Module.Flat Γ(X, ⊤) V] [Module.FinitePresentation Γ(X, ⊤) V] (r : ℕ) :
    ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsOpenImmersion j ∧ IsClosedImmersion j ∧
      ∀ (T : Scheme.{0}) (f : T ⟶ X),
        (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
          letI : Algebra Γ(X, ⊤) k := (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (p ≫ f)).toAlgebra
          Module.finrank k (k ⊗[Γ(X, ⊤)] V) = r) ↔
            ∃! q : T ⟶ Z, q ≫ j = f := by
  let U := FlatModuleRankOpen.flatModuleRankOpen (R := Γ(X, ⊤)) V r
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]
    exact FlatModuleRankOpen.flatModuleRankOpen_isClosed V r)
  let j : U.toScheme ⟶ X := U.ι ≫ inv X.toSpecΓ
  refine ⟨U.toScheme, j, inferInstance, inferInstance, ?_⟩
  intro T f
  have hpred :
      (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
        letI : Algebra Γ(X, ⊤) k := (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (p ≫ f)).toAlgebra
        Module.finrank k (k ⊗[Γ(X, ⊤)] V) = r) ↔
      (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
        letI : Algebra Γ(X, ⊤) k := (Spec.preimage (p ≫ (f ≫ X.toSpecΓ))).hom.toAlgebra
        Module.finrank k (k ⊗[Γ(X, ⊤)] V) = r) := by
    constructor
    · intro h k hk ha p
      rw [← Category.assoc, CoefficientPoints.schemePointCoefficientMap_preimage]
      exact h k p
    · intro h k hk ha p
      have hp := h k p
      rw [← Category.assoc, CoefficientPoints.schemePointCoefficientMap_preimage] at hp
      exact hp
  refine hpred.trans ((FlatModuleRankOpen.flatModuleRankOpen_classifies V r (f ≫ X.toSpecΓ)).trans ?_)
  have hlift (q : T ⟶ U.toScheme) : q ≫ U.ι = f ≫ X.toSpecΓ ↔ q ≫ j = f := by
    constructor
    · intro h
      change q ≫ U.ι ≫ inv X.toSpecΓ = f
      rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    · intro h
      have he := congrArg (fun a : T ⟶ X => a ≫ X.toSpecΓ) h
      change (q ≫ U.ι ≫ inv X.toSpecΓ) ≫ X.toSpecΓ = f ≫ X.toSpecΓ at he
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using he
  exact existsUnique_congr hlift

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.FlatRankLocus
