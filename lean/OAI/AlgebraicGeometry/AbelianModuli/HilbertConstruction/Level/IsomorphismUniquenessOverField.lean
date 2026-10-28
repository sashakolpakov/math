import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityOverField

/-! # Isomorphism Uniqueness Over Field -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.IsomorphismUniquenessOverField

noncomputable section

/-! Full-level polarized isomorphisms over a field are unique at every level at least three. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem polarizedIsomorphisms_subsingleton_overField (hN : 3 ≤ N) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso A B) := by
  refine ⟨fun e d => ?_⟩
  have h := congrArg (fun f : Moduli.Isomorphisms.LevelPreservingIso A A => f.abelian.hom)
    ((e.trans d.symm).eq_refl_overField A hN)
  have he : e.abelian.hom ≫ d.abelian.inv = 𝟙 A.abelian.scheme := h
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e d
  apply (cancel_mono d.abelian.inv).mp
  exact he.trans d.abelian.hom_inv_id.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.IsomorphismUniquenessOverField
