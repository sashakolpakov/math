import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobal

/-! # Exact Refined Global Target -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobalTarget.Comparison

noncomputable section

/-! Exact coefficient transport of a geometric common-cover square,
composed while the frame complexes remain abstract. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
universe u v w z
variable {D : Type u} [Category.{v} D] [Abelian D]
  {L₀ L₁ L₂ : CochainComplex D ℕ} {r : L₀ ⟶ L₁} {s : L₁ ⟶ L₂} (i : ℕ)
  {B₁ B₂ : D} {h : L₂.homology i ⟶ B₁} {e : L₀.homology i ⟶ B₂} {g : B₂ ⟶ B₁}
  (hg : homologyMap r i ≫ homologyMap s i ≫ h = e ≫ g)
  {C : Type w} [Category.{z} C] [Abelian C]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {K₀ K₁ K₂ : CochainComplex C ℕ}
  (a : (F.mapHomologicalComplex (.up ℕ)).obj K₀ ≅ L₀)
  (b : (F.mapHomologicalComplex (.up ℕ)).obj K₁ ≅ L₁)
  (c : (F.mapHomologicalComplex (.up ℕ)).obj K₂ ≅ L₂)
  (f : K₀ ⟶ K₁) (f' : K₁ ⟶ K₂)
  (hf : (F.mapHomologicalComplex (.up ℕ)).map f ≫ b.hom = a.hom ≫ r)
  (hf' : (F.mapHomologicalComplex (.up ℕ)).map f' ≫ c.hom = b.hom ≫ s)

abbrev target := RefinedInferred.Comparison.target
  (GeometricComparison.ExactHomology.ExactHomologyComparison.naturality F (.up ℕ) a b f r hf i).symm
  (GeometricComparison.ExactHomology.ExactHomologyComparison.naturality F (.up ℕ) b c f' s hf' i).symm hg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobalTarget.Comparison
