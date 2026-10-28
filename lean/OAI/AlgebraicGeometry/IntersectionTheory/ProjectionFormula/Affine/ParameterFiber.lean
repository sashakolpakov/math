import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterGerms
import Mathlib.RingTheory.Polynomial.Ideal

/-! # Parameter Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterFiber

noncomputable section

/-! For an actual affine-line parameter, its scalar fiber is exactly
the nonunit locus of the regular germ of the translated coordinate. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry IsLocalRing
open scoped _root_.Polynomial

universe u

variable (k : Type u) [Field k]

def point (a : k) : PrimeSpectrum k[X] :=
  ⟨RingHom.ker (Polynomial.evalRingHom a),
    Ideal.isPrime_bot.comap (Polynomial.evalRingHom a)⟩

theorem mem_iff (p : PrimeSpectrum k[X]) (a : k) :
    Polynomial.X - Polynomial.C a ∈ p.asIdeal ↔ p = point k a := by
  constructor
  · intro h
    apply PrimeSpectrum.ext
    apply Eq.symm
    apply (RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom a)
      (fun c => ⟨Polynomial.C c, Polynomial.eval_C⟩)).eq_of_le p.isPrime.ne_top
    rw [Polynomial.ker_evalRingHom]
    exact Ideal.span_le.mpr (fun b hb => (Set.mem_singleton_iff.mp hb).symm ▸ h)
  · rintro rfl
    change Polynomial.evalRingHom a (Polynomial.X - Polynomial.C a) = 0
    simp

theorem point_spec (a : k) :
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (closedPoint k) = point k a := by
  apply PrimeSpectrum.ext
  change (maximalIdeal k).comap (Polynomial.evalRingHom a) = RingHom.ker (Polynomial.evalRingHom a)
  rw [maximalIdeal_eq_bot]
  rfl

theorem toStalk_unit (p : PrimeSpectrum k[X]) (f : k[X]) :
    IsUnit (StructureSheaf.toStalk k[X] p f) ↔ f ∉ p.asIdeal := by
  have he : (StructureSheaf.stalkIso k[X] p)
      (algebraMap k[X] (Localization.AtPrime p.asIdeal) f) = StructureSheaf.toStalk k[X] p f :=
    (StructureSheaf.stalkIso k[X] p).commutes f
  exact (iff_of_eq (congrArg IsUnit he.symm)).trans
    ((MulEquiv.isUnit_map (StructureSheaf.stalkIso k[X] p)).trans
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p.asIdeal) p.asIdeal f))

variable {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k[X]))

def germ (x : Z) (a : k) : Z.presheaf.stalk x :=
  t.stalkMap x (StructureSheaf.toStalk k[X] (t x) (Polynomial.X - Polynomial.C a))

theorem germ_mem_maximalIdeal (x : Z) (a : k) :
    germ k t x a ∈ maximalIdeal (Z.presheaf.stalk x) ↔ t x = point k a := by
  rw [mem_maximalIdeal, mem_nonunits_iff, germ, isUnit_map_iff,
    toStalk_unit, not_not, mem_iff]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterFiber
