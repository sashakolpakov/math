import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralObject

/-! # Zero Source Cone -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroSourceCone

noncomputable section

/-! The native cone of a map from a zero complex is isomorphic to its
target by the canonical right inclusion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R]
  {P Q : CochainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q) (h : IsZero P)

def iso : Q ≅ mappingCone f where
  hom := mappingCone.inr f
  inv := mappingCone.desc f 0 (𝟙 Q) (by rw [h.eq_zero_of_src f]; simp)
  hom_inv_id := mappingCone.inr_desc _ _ _ _
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply mappingCone.ext_from f (n + 1) n rfl
    · exact ((HomologicalComplex.eval _ _ (n + 1)).map_isZero h).eq_of_src _ _
    · simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.comp_id,
        mappingCone.inr_f_desc_f_assoc, Category.id_comp]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroSourceCone
