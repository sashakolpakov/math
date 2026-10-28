import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterFiber

/-! # Parameter Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.ParameterFiber

noncomputable section

/-! A prime in an ambient stalk contains the parameter germ exactly
when its actual image point lies in the corresponding scalar fiber. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

variable {Z : Scheme} (t : Z ⟶ Spec (.of ℂ[X])) (x : Z)

theorem mem_iff (p : Spec (Z.presheaf.stalk x)) (a : ℂ) :
    Affine.ParameterFiber.germ ℂ t x a ∈ p.asIdeal ↔
      t (Z.fromSpecStalk x p) = Affine.ParameterFiber.point ℂ a := by
  have he := congrArg (fun g : Spec (Z.presheaf.stalk x) ⟶ Spec (.of ℂ[X]) => g p)
    (Scheme.SpecMap_stalkMap_fromSpecStalk t (x := x))
  change (Spec (.of ℂ[X])).fromSpecStalk (t x) ((Spec.map (t.stalkMap x)) p) =
    t (Z.fromSpecStalk x p) at he
  have hp : t (Z.fromSpecStalk x p) =
      PrimeSpectrum.comap ((t.stalkMap x).hom.comp (StructureSheaf.toStalk ℂ[X] (t x)).hom) p := by
    rw [← he, Spec.fromSpecStalk_eq']
    rfl
  calc
    _ ↔ Polynomial.X - Polynomial.C a ∈ (t (Z.fromSpecStalk x p)).asIdeal := by rw [hp]; rfl
    _ ↔ _ := Affine.ParameterFiber.mem_iff _ _ _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.ParameterFiber
