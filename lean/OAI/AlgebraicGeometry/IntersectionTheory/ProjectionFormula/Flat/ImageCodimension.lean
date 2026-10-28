import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Image Codimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ImageCodimension

noncomputable section

/-! Flat morphisms do not increase point codimension. The proof lifts
actual strict specialization chains through the generalizing map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

theorem coheight_le {X Y : Scheme} (f : X ⟶ Y) [Flat f]
    (p : ℕ) (x : X) (hx : coheight x ≤ p) : coheight (f x) ≤ p := by
  induction p generalizing x with
  | zero =>
    apply coheight_le_coe_iff.mpr
    intro y hy
    obtain ⟨z, hz, hfz⟩ := Flat.generalizingMap f (Scheme.le_iff_specializes.mp hy.le)
    have hxz : x < z := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hz, fun hzx => hy.not_ge (by
      rw [← hfz]
      exact Scheme.le_iff_specializes.mpr ((Scheme.le_iff_specializes.mp hzx).map f.continuous))⟩
    exact False.elim (not_lt_of_ge (zero_le : (0 : ℕ∞) ≤ coheight z)
      (coheight_le_coe_iff.mp hx z hxz))
  | succ p ih =>
    apply coheight_le_coe_iff.mpr
    intro y hy
    obtain ⟨z, hz, hfz⟩ := Flat.generalizingMap f (Scheme.le_iff_specializes.mp hy.le)
    have hxz : x < z := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hz, fun hzx => hy.not_ge (by
      rw [← hfz]
      exact Scheme.le_iff_specializes.mpr ((Scheme.le_iff_specializes.mp hzx).map f.continuous))⟩
    have hzdim : coheight z ≤ p := by
      have h := coheight_le_coe_iff.mp hx z hxz
      rw [Nat.cast_add, Nat.cast_one, ENat.lt_natCast_add_one_iff] at h
      exact h
    rw [← hfz, Nat.cast_add, Nat.cast_one, ENat.lt_natCast_add_one_iff]
    exact ih z hzdim

theorem image_codimension_le {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) [Flat f.left] (m n p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (A : X.DimensionCycleSupport p) : Y.supportCodimension (ProperCycleLinearity.imageSupport f A.val) ≤ p := by
  have h := coheight_le f.left p (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (IntermediateSupports.support_coheight X m p A).le
  let B : Y.DimensionCycleSupport (Y.supportCodimension (ProperCycleLinearity.imageSupport f A.val)) := ⟨_, rfl⟩
  have he := IntermediateSupports.support_coheight Y n _ B
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint B.val = f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) := irreducibleSetEquivPoints.apply_symm_apply _
  rw [hp] at he
  have hdim : (Y.supportCodimension (ProperCycleLinearity.imageSupport f A.val) : ℕ∞) ≤ p := he.symm.trans_le h
  exact_mod_cast hdim

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ImageCodimension
