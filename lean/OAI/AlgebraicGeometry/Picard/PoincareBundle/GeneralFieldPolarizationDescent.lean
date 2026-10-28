import OAI.AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldHomDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PolarizationComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTypeDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFormulaRecovery

/-! # General Field Polarization Descent -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldPolarizationDescent

/-! Polarization descent over an arbitrary field, with full scheme-valued maximal isotropy and no characteristic restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) {δ : Fin a → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- Maximal isotropy constructs the unique quotient polarization over the original field, with its finite-flat degree, geometric kernel type, and positivity all proved. -/
theorem existsUnique_polarization (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : Geometric.WeilIsotropy.SelfAnnihilating DA pol f n hn hf) :
    ∃! m : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      f.hom ≫ m.isogeny.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ n := by
  obtain ⟨m, hm, hu⟩ := GeneralFieldHomDescent.Isogeny.existsUnique_isogeny DA DB pol f n hn hnd hf hlag
  have hlocal : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Spec (.of k)),
      ∃ r : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (DB.pullback s) δ, m.pullback s = r.isogeny :=
    Geometric.PolarizationComparison.exists_polarization_eq DA DB pol f n hn hnd hf hlag m hm
  have htype : m.HasPolarizationType δ :=
    PolarizationTypeDescent.polarization_type_of_geometric_baseChanges m δ (by
      intro K _ _ s
      obtain ⟨r, hr⟩ := hlocal K s
      rw [hr]
      exact r.kernelType)
  have hpositive : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Spec (.of k)),
      AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber DB m.hom K s := by
    intro K _ _ s
    obtain ⟨r, hr⟩ := hlocal K s
    have heq : (Over.pullback s).map m.hom = r.isogeny.hom := congrArg (fun t => t.hom) hr
    apply FiberFormulaRecovery.positive DB m.hom K s
    rw [heq]
    exact Reference.PositiveFormula.of_polarization (DB.pullback s) r
  let p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ := ⟨m, htype, hpositive⟩
  refine ⟨p, hm, ?_⟩
  intro r hr
  exact Canonical.WeilPolarizationDescent.polarization_ext r p (hu r.isogeny hr)

/-- PoincareBundle for q-power torsion: q is prime to the polarization degree but may equal the field characteristic, and all infinitesimal subgroup-scheme tests are retained. -/
theorem existsUnique_primePower_polarization (q h : ℕ) (hq : q.Prime) (hqd : q.Coprime (∏ i, δ i))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ h) = 1)
    (hlag : Geometric.WeilIsotropy.SelfAnnihilating DA pol f (q ^ h) (pow_pos hq.pos h) hf) :
    ∃! m : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      f.hom ≫ m.isogeny.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ (q ^ h) :=
  existsUnique_polarization DA DB pol f (q ^ h) (pow_pos hq.pos h) ((hqd.pow_right 2).pow_left h) hf hlag

end AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldPolarizationDescent

namespace AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldPolarizationDescent.Theorem

/-! The PoincareBundle conclusion, with the prime-to-degree assumption and uniqueness among all actual polarization homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) {δ : Fin a → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- A Lagrangian q-power kernel constructs a polarization of unchanged type; any polarization satisfying the equation has the same actual isogeny, regardless of its recorded type. -/
theorem polarization_descent_through_maximal_isotropic_kernel
    (q h : ℕ) (hq : q.Prime) (hqpol : q.Coprime ((∏ i, δ i) ^ 2))
    (hkernel : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ h) = 1)
    (hlagrangian : Geometric.WeilIsotropy.SelfAnnihilating DA pol f (q ^ h) (pow_pos hq.pos h) hkernel) :
    ∃ p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      (f.hom ≫ p.isogeny.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ (q ^ h)) ∧
      ∀ (ε : Fin a → ℕ) (r : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB ε),
        f.hom ≫ r.isogeny.hom ≫ DualMaps.representedDualMap
          (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
            pol.isogeny.hom ^ (q ^ h) → r.isogeny = p.isogeny := by
  have hqd : q.Coprime (∏ i, δ i) := (Nat.coprime_pow_right_iff (by decide : 0 < 2) q (∏ i, δ i)).mp hqpol
  obtain ⟨p, hp, _⟩ := existsUnique_primePower_polarization
    DA DB pol f q h hq hqd hkernel hlagrangian
  obtain ⟨m, _, hu⟩ := GeneralFieldHomDescent.Isogeny.existsUnique_isogeny DA DB pol f
    (q ^ h) (pow_pos hq.pos h) (hqpol.pow_left h) hkernel hlagrangian
  refine ⟨p, hp, ?_⟩
  intro ε r hr
  exact (hu r.isogeny hr).trans (hu p.isogeny hp).symm

end AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldPolarizationDescent.Theorem

end

end OAI
