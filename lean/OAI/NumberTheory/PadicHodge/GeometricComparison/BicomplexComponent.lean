import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ComponentHomology

/-! # Bicomplex Component -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComponent.BicomplexComponentHomology

noncomputable section

/-! A single total homology map only uses the components on its
corresponding finite diagonal of a first-quadrant bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)} [K.HasTotal (.up ℕ)] [L.HasTotal (.up ℕ)]
  (a b : K ⟶ L) (i : ℕ)
  (h : ∀ q r, q + r = i → (a.f q).f r = (b.f q).f r)

include h in
theorem component : (HomologicalComplex₂.total.map a (.up ℕ)).f i =
    (HomologicalComplex₂.total.map b (.up ℕ)).f i := by
  apply HomologicalComplex₂.total.hom_ext
  intro q r hi
  exact (HomologicalComplex₂.ιTotal_map K L a (.up ℕ) q r i hi).trans
    ((congrArg (fun x => x ≫ L.ιTotal (.up ℕ) q r i hi) (h q r hi)).trans
      (HomologicalComplex₂.ιTotal_map K L b (.up ℕ) q r i hi).symm)

include h in
theorem homology : HomologicalComplex.homologyMap (HomologicalComplex₂.total.map a (.up ℕ)) i =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map b (.up ℕ)) i :=
  CechPresheaf.ComponentHomology.CechPresheafComponentHomology.homology_of_component _ _ i (component a b i h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComponent.BicomplexComponentHomology
