import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedComposites
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Quotient

/-! # Multiplication Dual Factor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Once the original PEL isogeny is multiplication followed by a
family isomorphism, its original polarization equation forces the
matching multiplication formula for its actual dual map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {R : Type} [CommRing R] {S : Scheme} {g N : ℕ}
  {P Q : PEL.PELFamilyData R g N S} (a : (ZMod N)ˣ) (n : ℕ)
  (e : PELIsogenies.PELIsogeny P Q (n ^ 2)) (j : PELModuli.PELFamilyIso (P.shiftMarking a) Q)
  (he : e.isogeny.hom = ((𝟙 P.abelian.scheme) ^ n) ≫ j.abelian.hom)

include he in
theorem PELIsogenies.PELIsogeny.dual_eq_of_multiplication_factor :
    e.dualHom = j.dual.inv ≫ ((𝟙 P.dual.abelian.scheme) ^ n) := by
  have := CentralAction.Quotient.Construction.isogeny_effectiveEpi e.isogeny
  have := CentralAction.Quotient.Construction.isogeny_effectiveEpi P.polarizationMap
  have hfactor : e.isogeny.hom ≫ j.abelian.inv = (𝟙 P.abelian.scheme) ^ n := by
    rw [he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hq : Epi ((𝟙 P.abelian.scheme) ^ n) :=
    hfactor ▸ (inferInstanceAs (Epi (e.isogeny.hom ≫ j.abelian.inv)))
  apply (cancel_epi (((𝟙 P.abelian.scheme) ^ n) ≫ P.polarizationMap.hom ≫ j.dual.hom)).mp
  have hleft : (((𝟙 P.abelian.scheme) ^ n) ≫ P.polarizationMap.hom ≫ j.dual.hom) ≫ e.dualHom =
      P.polarizationMap.hom ^ (n ^ 2) := by
    calc
      _ = ((𝟙 P.abelian.scheme) ^ n) ≫ (P.polarizationMap.hom ≫ j.dual.hom) ≫ e.dualHom := by
        simp only [Category.assoc]
      _ = ((𝟙 P.abelian.scheme) ^ n) ≫ (j.abelian.hom ≫ Q.polarizationMap.hom) ≫ e.dualHom := by
        rw [j.polarization]
      _ = e.isogeny.hom ≫ Q.polarizationMap.hom ≫ e.dualHom := by
        rw [he]
        simp only [Category.assoc]
      _ = P.polarizationMap.hom ^ (n ^ 2) := e.polarization
  rw [hleft]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp, ← pow_mul, pow_two]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
