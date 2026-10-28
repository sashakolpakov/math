import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalRepresentation

/-! # Scheme Weil Canonical Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilCanonicalIsotropy

noncomputable section

/-! Original full scheme-theoretic maximal isotropy recovers the canonical represented Weil annihilator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)

/-- The full original-field annihilator implies the actual canonical Weil self-annihilator, with every scheme-valued test retained. -/
theorem canonical (h : SchemeWeilIsotropy.SelfAnnihilating D ell f n hn hker) :
    Canonical.WeilData.SelfAnnihilating D ell n hn (Kernel.ContainmentMap.torsionMap f.hom n hker) := by
  intro T y
  have hr := OrthogonalRepresentation.represented f.hom n hker
    (SchemeWeilIsotropy.value D ell n hn) h T y
  constructor
  · intro hy
    apply hr.mp
    intro U a x
    exact (PoincareBundle.Field.WeilCanonicalComparison.eq_one_iff D ell n hn _ _).mp (hy U a x)
  · intro hy
    have hv := hr.mpr hy
    intro U a x
    exact (PoincareBundle.Field.WeilCanonicalComparison.eq_one_iff D ell n hn _ _).mpr (hv U a x)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilCanonicalIsotropy
