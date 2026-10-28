import OAI.AlgebraicGeometry.Picard.PoincareBundle.Epi
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldPolarizationDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilGeometricBridge

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scheme

noncomputable section

/-!
# PoincareBundle from the original full scheme-theoretic maximal-isotropy hypothesis

The hypothesis below quantifies over all test schemes over the original field.
Geometric self-annihilation and compatibility of the actual Weil pairing are
proved consequences, not additional assumptions. The conclusion is an actual
polarization with geometric positivity and unchanged type, and uniqueness
among every polarization homomorphism satisfying the dual pullback equation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

/-- The expanded natural statement uses only original-field scheme-valued maximal isotropy. -/
def Statement : Prop :=
  ∀ (k : Type) [Field k] (a : ℕ) (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k)))
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (δ : Fin a → ℕ)
    (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (q h : ℕ) (hq : q.Prime),
    q.Coprime ((∏ i, δ i) ^ 2) →
    ∀ (hkernel : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme),
      x ≫ f.hom = 1 → x ^ (q ^ h) = 1),
    (∀ (T : Over (Spec (.of k))) (y : T ⟶ A.scheme) (hy : y ^ (q ^ h) = 1),
      (∀ (U : Over (Spec (.of k))) (b : U ⟶ T) (x : U ⟶ A.scheme) (hx : x ≫ f.hom = 1),
        PoincareBundle.Field.WeilPairing.value DA pol.isogeny (q ^ h) (pow_pos hq.pos h)
          x (hkernel U x hx) (b ≫ y)
          (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) = 1) ↔ y ≫ f.hom = 1) →
    ∃ p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      (f.hom ≫ p.isogeny.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ (q ^ h)) ∧
      ∀ (ε : Fin a → ℕ) (r : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB ε),
        f.hom ≫ r.isogeny.hom ≫ DualMaps.representedDualMap
          (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
            pol.isogeny.hom ^ (q ^ h) → r.isogeny = p.isogeny

/-- The original maximal-isotropic kernel yields the preserved PoincareBundle polarization conclusion. -/
theorem proved : Statement := by
  intro k _ a A B DA DB δ pol f q h hq hqpol hkernel hlagrangian
  have hfull : SchemeWeilIsotropy.SelfAnnihilating DA pol.isogeny f
      (q ^ h) (pow_pos hq.pos h) hkernel := by
    intro T y
    exact hlagrangian T y.val y.property
  exact GeneralFieldPolarizationDescent.Theorem.polarization_descent_through_maximal_isotropic_kernel
    DA DB pol f q h hq hqpol hkernel
    (SchemeWeilGeometricBridge.geometric DA pol f (q ^ h) (pow_pos hq.pos h) hkernel hfull)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scheme
