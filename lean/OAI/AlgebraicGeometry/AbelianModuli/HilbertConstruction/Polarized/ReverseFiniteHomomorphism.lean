import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ReverseHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.MultiplicationFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteSourceCover

/-! # Reverse Finite Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A polarized full-level abelian object has an actual finite reverse group homomorphism from its dual, over the original base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_finite_reverseHomomorphism (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hδ : ∀ i, 0 < δ i) :
    ∃ m : A.dual.abelian.scheme ⟶ A.abelian.scheme, IsMonHom m ∧ IsFinite m.left ∧
      A.polarization.isogeny.hom ≫ m = A.abelian.multiplication ((∏ i, δ i) ^ 2) ∧
      m ≫ A.polarization.isogeny.hom = A.dual.abelian.multiplication ((∏ i, δ i) ^ 2) := by
  obtain ⟨m, hm, hl, hr⟩ := A.polarization.kernelType.exists_reverseHomomorphism hδ
  have hd : 0 < (∏ i, δ i) ^ 2 := pow_pos (Finset.prod_pos (fun i _ => hδ i)) 2
  have : IsProper (m.left ≫ A.abelian.scheme.hom) :=
    m.w.symm ▸ inferInstanceAs (IsProper A.dual.abelian.scheme.hom)
  have : IsProper m.left := IsProper.of_comp m.left A.abelian.scheme.hom
  have hcomp : IsFinite (A.polarization.isogeny.hom.left ≫ m.left) := by
    change IsFinite (A.polarization.isogeny.hom ≫ m).left
    rw [hl]
    exact A.multiplication_isFinite _ hd
  exact ⟨m, hm, Proper.FiniteSourceCover.proper_isFinite_of_surjective_precomp A.polarization.isogeny.hom.left m.left,
    hl, hr⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
