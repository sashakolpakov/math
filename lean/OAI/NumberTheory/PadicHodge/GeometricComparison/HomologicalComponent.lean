import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ComponentHomology

/-! # Homological Component -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HomologicalComponent.HomologicalComponentHeterogeneous

noncomputable section

/-! Transport component agreement to homology while keeping the
two presentations of the complexes separate. -/
open _root_.CategoryTheory

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  {M N K L : CochainComplex A ℕ}

theorem homology (a : M ⟶ K) (b : N ⟶ L) (j : ℕ)
    (hM : M = N) (hK : K = L) (h : HEq (a.f j) (b.f j)) :
    HEq (HomologicalComplex.homologyMap a j) (HomologicalComplex.homologyMap b j) := by
  cases hM
  cases hK
  exact heq_of_eq (CechPresheaf.ComponentHomology.CechPresheafComponentHomology.homology_of_component a b j (eq_of_heq h))

theorem composite (a : M ⟶ N) (r : N ⟶ K) (b : M ⟶ K) (j : ℕ)
    (h : a.f j ≫ r.f j = b.f j) :
    HomologicalComplex.homologyMap a j ≫ HomologicalComplex.homologyMap r j =
      HomologicalComplex.homologyMap b j :=
  (HomologicalComplex.homologyMap_comp a r j).symm.trans
    (CechPresheaf.ComponentHomology.CechPresheafComponentHomology.homology_of_component (a ≫ r) b j h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HomologicalComponent.HomologicalComponentHeterogeneous
