import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients
import OAI.AlgebraicTopology.Cohomology.Singular.Functor

/-! # Formulas -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Formulas

noncomputable section

/-!
# The ordinary simplicial coboundary and pullback formulas

The degreewise objects of `simplicialCochains` are all functions on simplices.
The lemmas below identify its differential with the alternating face formula
and its contravariant maps with precomposition on simplices. Thus the
opposite-category construction has the standard cochain operations.

The categorical proofs generalize the checked `OppositeCochainAudit.lean`
from the frozen September 2026 audit from rational coefficients to an arbitrary
module over a ring. No Hodge-theoretic comparison is asserted here.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R]

/-- Evaluating the cochain differential is the alternating sum of face evaluations. -/
theorem evaluation_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (s : K _⦋n + 1⦌) :
    (Basic.simplicialCochains K M).d n (n + 1) ≫ Coefficients.simplicialEvaluation K M s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • Coefficients.simplicialEvaluation K M (K.δ i s) := by
  simpa only [Coefficients.simplicialEvaluation, Basic.simplicialCochains, Basic.oppositeSimplicialChains,
    HomologicalComplex.unop_d, unop_comp, unop_sum, unop_zsmul] using
    congrArg Quiver.Hom.unop (K.ιChainComplex_d (R := op M) s)

/-- A simplicial pullback evaluates on the image of the simplex. -/
theorem evaluation_pullback (M : ModuleCat.{0} R) {K L : SSet.{0}}
    (f : K ⟶ L) {n : ℕ} (s : K _⦋n⦌) :
    (Functor.simplicialPullback M f).f n ≫ Coefficients.simplicialEvaluation K M s =
      Coefficients.simplicialEvaluation L M (f.app _ s) := by
  change ((SSet.chainComplexMap f (op M)).f n).unop ≫
    Coefficients.simplicialEvaluation K M s = Coefficients.simplicialEvaluation L M (f.app _ s)
  simpa only [Coefficients.simplicialEvaluation, unop_comp] using
    congrArg Quiver.Hom.unop
      (SSet.ι_chainComplexMap_f (X := K) (Y := L) (R := op M) f s)

/-- The alternating face formula for an individual module-valued cochain. -/
theorem evaluation_coboundary_apply (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Basic.simplicialCochains K M).X n) (s : K _⦋n + 1⦌) :
    Coefficients.simplicialEvaluation K M s ((Basic.simplicialCochains K M).d n (n + 1) c) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • Coefficients.simplicialEvaluation K M (K.δ i s) c := by
  simpa [ModuleCat.comp_apply] using
    ConcreteCategory.congr_hom (evaluation_coboundary K M s) c

/-- The precomposition formula for an individual module-valued cochain. -/
theorem evaluation_pullback_apply (M : ModuleCat.{0} R) {K L : SSet.{0}}
    (f : K ⟶ L) {n : ℕ} (c : (Basic.simplicialCochains L M).X n) (s : K _⦋n⦌) :
    Coefficients.simplicialEvaluation K M s ((Functor.simplicialPullback M f).f n c) =
      Coefficients.simplicialEvaluation L M (f.app _ s) c := by
  simpa [ModuleCat.comp_apply] using
    ConcreteCategory.congr_hom (evaluation_pullback M f s) c

/-- In ordinary function coordinates, the differential is the alternating face sum. -/
theorem degreewiseFunctionIso_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Basic.simplicialCochains K M).X n) (s : K _⦋n + 1⦌) :
    (Coefficients.degreewiseFunctionIso K M (n + 1)).hom
        ((Basic.simplicialCochains K M).d n (n + 1) c) s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.degreewiseFunctionIso K M n).hom c (K.δ i s) := by
  calc
    _ = Coefficients.simplicialEvaluation K M s ((Basic.simplicialCochains K M).d n (n + 1) c) :=
      Coefficients.degreewiseFunctionIso_hom_apply K M _ s
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        Coefficients.simplicialEvaluation K M (K.δ i s) c := evaluation_coboundary_apply K M c s
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun v : M => ((-1 : ℤ) ^ i.val) • v)
        (Coefficients.degreewiseFunctionIso_hom_apply K M c (K.δ i s)).symm

/-- In ordinary function coordinates, a simplicial pullback is precomposition. -/
theorem degreewiseFunctionIso_pullback (M : ModuleCat.{0} R) {K L : SSet.{0}}
    (f : K ⟶ L) {n : ℕ} (c : (Basic.simplicialCochains L M).X n) (s : K _⦋n⦌) :
    (Coefficients.degreewiseFunctionIso K M n).hom ((Functor.simplicialPullback M f).f n c) s =
      (Coefficients.degreewiseFunctionIso L M n).hom c (f.app _ s) := by
  calc
    _ = Coefficients.simplicialEvaluation K M s ((Functor.simplicialPullback M f).f n c) :=
      Coefficients.degreewiseFunctionIso_hom_apply K M _ s
    _ = Coefficients.simplicialEvaluation L M (f.app _ s) c := evaluation_pullback_apply M f c s
    _ = _ := (Coefficients.degreewiseFunctionIso_hom_apply L M c (f.app _ s)).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.Formulas
