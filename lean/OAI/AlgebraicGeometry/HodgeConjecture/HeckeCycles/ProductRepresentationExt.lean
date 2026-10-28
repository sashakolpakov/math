import Mathlib

/-! # Product Representation Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductRepresentationExt.CM

/-! Product representations are determined by their active restriction
and rational values when the rational away projection is surjective. -/

variable {R A B H : Type*} [Group R] [Group A] [Group B] [Group H]

theorem of_active_and_rational (r : R →* A × B)
    (hb : Function.Surjective (fun g => (r g).2)) (S T : A × B →* H)
    (hr : S.comp r = T.comp r) (ha : ∀ a : A, S (a, 1) = T (a, 1)) : S = T := by
  have haway (b : B) : S (1, b) = T (1, b) := by
    obtain ⟨g, hg⟩ := hb b
    have hp : ((r g).1, (1 : B)) * (1, b) = r g := by
      apply Prod.ext
      · simp
      · simpa using hg.symm
    apply mul_left_cancel (a := S ((r g).1, 1))
    calc
      _ = S (r g) := (S.map_mul _ _).symm.trans (congrArg S hp)
      _ = T (r g) := DFunLike.congr_fun hr g
      _ = T ((r g).1, 1) * T (1, b) := (congrArg T hp.symm).trans (T.map_mul _ _)
      _ = _ := congrArg (fun h : H => h * T (1, b)) (ha (r g).1).symm
  apply MonoidHom.ext
  rintro ⟨a, b⟩
  have hp : (a, b) = (a, (1 : B)) * (1, b) := by simp
  rw [hp, map_mul, map_mul, ha, haway]

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductRepresentationExt.CM
