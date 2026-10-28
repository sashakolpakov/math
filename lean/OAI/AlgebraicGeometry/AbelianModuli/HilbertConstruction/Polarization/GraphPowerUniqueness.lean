import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationPairs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.MultiplicationFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TorsionHomCancellation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.UnaryTensorPower

/-! # Graph Power Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On a polarized abelian variety, a positive tensor power of the
canonical graph bundle determines any polarization map with the same
normalized symmetric Poincare formula. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (hδ : ∀ i, 0 < δ i)
variable (q : A.abelian.scheme ⟶ A.dual.abelian.scheme) [IsMonHom q]
variable (Lp Lq : Line.Bundles.LineBundle A.abelian.scheme.left)
variable (ep : (((A.dual.poincareAt A.polarization.isogeny.hom).tensor
  (Lp.pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
    (Lp.pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
      (Lp.pullback μ[A.abelian.scheme].left).sheaf)
variable (eq : (((A.dual.poincareAt q).tensor
  (Lq.pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
    (Lq.pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
      (Lq.pullback μ[A.abelian.scheme].left).sheaf)

include hδ Lp Lq ep eq in
theorem PolarizationData.PolarizedAbelianWithFullLevel.polarization_hom_eq_of_graphPower_class (d : ℕ) (hd : 0 < d)
    (hgraph : Line.Bundles.LineBundle.classOf A.graphBundle ^ d = Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle A.dual q) ^ d) :
    A.polarization.isogeny.hom = q := by
  let : IsFinite (A.dual.abelian.torsionScheme (2 * d)).hom :=
    A.dual_torsionScheme_isFinite hδ (2 * d) (Nat.mul_pos (by decide) hd)
  apply Finite.TorsionHomCancellation.abelian_hom_pow_injective_of_finite_torsion A.abelian A.dual.abelian (2 * d)
  exact GraphPower.PolarizationPairs.graphPower_determines_hom_power A.dual A.polarization.isogeny.hom q d hgraph
    (fun x y => Polarization.PairSymmetry.polarizationPairClass_symmetric A.dual A.polarization.isogeny.hom Lp ep x y)
    (fun x y => Polarization.PairSymmetry.polarizationPairClass_symmetric A.dual q Lq eq x y)

include hδ Lp Lq ep eq in
theorem PolarizationData.PolarizedAbelianWithFullLevel.polarization_hom_eq_of_graphPower_iso (d : ℕ) (hd : 0 < d)
    (e : (A.graphBundle.tensorPower d).sheaf ≅ ((PoincareGraph.Bundles.poincareGraphBundle A.dual q).tensorPower d).sheaf) :
    A.polarization.isogeny.hom = q := by
  apply A.polarization_hom_eq_of_graphPower_class hδ q Lp Lq ep eq d hd
  have h : Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d) =
      Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle A.dual q).tensorPower d) := Quotient.sound ⟨e⟩
  simpa only [Line.Bundles.LineBundle.classOf_tensorPower] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
