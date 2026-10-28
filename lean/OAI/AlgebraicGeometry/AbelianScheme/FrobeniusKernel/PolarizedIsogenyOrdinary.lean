import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotients
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Torsion

/-! # Polarized Isogeny Ordinary -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedIsogenyOrdinary.Construction

noncomputable section

/-! The actual source polarization supplies finite torsion and
divisible geometric points. Thus a geometric isogeny preserves the
torsion count without an additional ordinary-splitting hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem polarized_torsionScheme_finite {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n) :
    IsFinite (A.torsionScheme n).hom := by
  have : IsFinite (A.multiplication n).left := CartierDuality.Torsion.Construction.Multiplication.finite_positive_power A D ell n hn
  exact inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd
    (A.multiplication n).left η[A.scheme].left))

theorem polarizedIsogeny_torsionCard_preserved {k : Type u} [Field k] [IsAlgClosed k]
    {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n) :
    Nat.card (A.torsionPoints n (Over.mk (𝟙 (Spec (.of k))))) =
      Nat.card (B.torsionPoints n (Over.mk (𝟙 (Spec (.of k))))) := by
  have : IsFinite (A.torsionScheme n).hom := polarized_torsionScheme_finite A D ell n hn
  exact OrdinaryQuotients.Construction.isogeny_qRank_preserved A B f n

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedIsogenyOrdinary.Construction
