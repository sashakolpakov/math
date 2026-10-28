import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilCanonicalIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.WeilIsotropy

/-! # Scheme Weil Geometric Bridge -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilGeometricBridge

noncomputable section

/-! Geometric full maximal isotropy follows from the original full scheme-theoretic hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)

/-- The original full scheme-valued annihilator condition implies the geometric hypothesis of the preserved descent theorem. No base-change compatibility is assumed. -/
theorem geometric (h : SchemeWeilIsotropy.SelfAnnihilating D pol.isogeny f n hn hker) :
    Geometric.WeilIsotropy.SelfAnnihilating D pol f n hn hker := by
  intro K _ _ s
  exact SchemeWeilCanonicalIsotropy.canonical (D.pullback s) (pol.pullback s).isogeny
    (f.pullback s) n hn (Kernel.ContainmentBaseChange.contained f n hker s)
    (SchemeWeilIsotropy.baseChange D pol.isogeny f n hn hker h s)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilGeometricBridge
