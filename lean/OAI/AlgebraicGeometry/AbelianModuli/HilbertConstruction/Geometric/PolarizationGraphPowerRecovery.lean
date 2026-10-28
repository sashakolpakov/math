import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphPowerUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.AdditionEuler

/-! # Polarization Graph Power Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The original geometric positivity hypotheses supply the normalized
formulas needed for graph-power recovery of a polarization on every
geometric field pullback of an arbitrary base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def PolarizationData.PolarizedAbelianWithFullLevel.withPolarization (p : PolarizationData.Polarization A.dual δ) : PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := A.abelian
  dual := A.dual
  polarization := p
  level := A.level

theorem PolarizationData.PolarizedAbelianWithFullLevel.polarization_graphPower_geometric_recovery (hδ : ∀ i, 0 < δ i)
    (p : PolarizationData.Polarization A.dual δ) (d : ℕ) (hd : 0 < d)
    (he : Line.Bundles.LineBundle.classOf A.graphBundle ^ d =
      Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle A.dual p.isogeny.hom) ^ d)
    (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S) :
    (Over.pullback f).map A.polarization.isogeny.hom = (Over.pullback f).map p.isogeny.hom := by
  let B := A.withPolarization p
  obtain ⟨Lp, ⟨ep⟩⟩ := (Geometric.AdditionEuler.PolarizedAbelianWithLevel.geometricPullback_normalizedPolarizationFormula A) K f
  obtain ⟨Lq, ⟨eq⟩⟩ := (Geometric.AdditionEuler.PolarizedAbelianWithLevel.geometricPullback_normalizedPolarizationFormula B) K f
  have : IsMonHom ((Over.pullback f).map p.isogeny.hom) :=
    inferInstanceAs (IsMonHom (p.isogeny.pullback f).hom)
  apply (A.pullback f).polarization_hom_eq_of_graphPower_class hδ
    ((Over.pullback f).map p.isogeny.hom) Lp Lq ep eq d hd
  let r := CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom f
  have h := congrArg (Line.Bundles.LineBundle.pullbackClassMonoidHom r) he
  rw [map_pow, map_pow] at h
  have hA : Line.Bundles.LineBundle.classOf (A.pullback f).graphBundle =
      Line.Bundles.LineBundle.pullbackClassMonoidHom r (Line.Bundles.LineBundle.classOf A.graphBundle) :=
    Quotient.sound ⟨A.graphBundle_baseChangeIso f⟩
  have hB : Line.Bundles.LineBundle.classOf (B.pullback f).graphBundle =
      Line.Bundles.LineBundle.pullbackClassMonoidHom r (Line.Bundles.LineBundle.classOf B.graphBundle) :=
    Quotient.sound ⟨B.graphBundle_baseChangeIso f⟩
  change Line.Bundles.LineBundle.pullbackClassMonoidHom r (Line.Bundles.LineBundle.classOf A.graphBundle) ^ d =
    Line.Bundles.LineBundle.pullbackClassMonoidHom r (Line.Bundles.LineBundle.classOf B.graphBundle) ^ d at h
  rw [← hA, ← hB] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
