import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalPoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Fiber

/-! # Rational Fiber -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalFiber

noncomputable section

/-! Triviality over a rational point is triviality on its actual
residue-field fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

namespace Construction.RationalFiberTriviality

variable {K : Type u} [Field K] {X S : Scheme.{u}}
variable (π : X ⟶ S) (t : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S) (hs : s ≫ t = 𝟙 _)

abbrev point := RationalPoint.Construction.RationalPointResidue.point s

def map : pullback π s ⟶ π.fiber (point s) :=
  pullback.map π s π (S.fromSpecResidueField (point s))
    (𝟙 X) (Spec.map (RationalPoint.Construction.RationalPointResidue.fieldMap s)) (𝟙 S)
    (by simp) (by simpa only [Category.comp_id] using (RationalPoint.Construction.RationalPointResidue.factor s).symm)

include hs in
theorem isIso_map : IsIso (RationalFiberTriviality.map π s) := by
  have := RationalPoint.Construction.RationalPointResidue.isIso_fieldMap t s hs
  dsimp only [RationalFiberTriviality.map]
  infer_instance

theorem map_first : RationalFiberTriviality.map π s ≫ π.fiberι (point s) = pullback.fst π s := by
  simp only [RationalFiberTriviality.map, Scheme.Hom.fiberι, pullback.map, pullback.lift_fst, Category.comp_id]

def iso (M : X.Modules)
    (e : (Scheme.Modules.pullback (pullback.fst π s)).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback π s)) :
    (Scheme.Modules.pullback (π.fiberι (point s))).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (point s)) := by
  have := isIso_map π t s hs
  have hi : inv (RationalFiberTriviality.map π s) ≫ pullback.fst π s = π.fiberι (point s) := by
    apply (cancel_epi (RationalFiberTriviality.map π s)).mp
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, map_first]
  exact (Scheme.Modules.pullbackCongr hi.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (inv (RationalFiberTriviality.map π s)) (pullback.fst π s)).app M).symm ≪≫
    (Scheme.Modules.pullback (inv (RationalFiberTriviality.map π s))).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (inv (RationalFiberTriviality.map π s))

end Construction.RationalFiberTriviality

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalFiber
