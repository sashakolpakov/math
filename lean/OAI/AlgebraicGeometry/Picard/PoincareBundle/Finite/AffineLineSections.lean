import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification

/-! # Affine Line Sections -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AffineLineSections

noncomputable section

/-! The actual section module of a line on a nonempty finite affine scheme is finite and nonzero over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  (L : Line.Bundles.LineBundle (Spec (.of R)))

/-- Actual global line sections, with their base-ring scalar action retained by restriction of scalars. -/
def sections : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k R)).obj ((moduleSpecΓFunctor (R := .of R)).obj L.sheaf)

/-- The geometric line's section module is finite over the base whenever the affine coordinate algebra is finite. -/
theorem finite [Module.Finite k R] : Module.Finite k (sections k R L) := by
  let M := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj L.sheaf
  have : Module.Invertible R M := Affine.Classification.globalSections_invertible L
  let : Module k M := Module.compHom M (algebraMap k R)
  have : IsScalarTower k R M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfinite : Module.Finite k M := Module.Finite.trans R M
  exact hfinite

/-- An invertible sheaf on a nonempty affine scheme has a nonzero actual section module. -/
theorem nontrivial [Nontrivial R] : Nontrivial (sections k R L) := by
  let M := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj L.sheaf
  have : Module.Invertible R M := Affine.Classification.globalSections_invertible L
  change Nontrivial M
  by_contra h
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
  have he : (0 : R) = 1 := eq_of_smul_eq_smul fun x : M => Subsingleton.elim (0 • x) (1 • x)
  exact zero_ne_one he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AffineLineSections
