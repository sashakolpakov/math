import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedInferred

/-! # Exact Refined Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobal.Comparison

noncomputable section

/-! Exact coefficient comparison followed by a fixed original
frame-to-global square, with the frame complexes chosen first. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
universe u v w z
variable {D : Type u} [Category.{v} D] [Abelian D]
  {L L' : CochainComplex D ℕ} {r : L ⟶ L'} (i : ℕ)
  {B : D} {h : L'.homology i ⟶ B} {e : L.homology i ⟶ B}
  (hg : homologyMap r i ≫ h = e)
  {C : Type w} [Category.{z} C] [Abelian C]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {K K' : CochainComplex C ℕ}
  (a : (F.mapHomologicalComplex (.up ℕ)).obj K ≅ L)
  (b : (F.mapHomologicalComplex (.up ℕ)).obj K' ≅ L')
  (f : K ⟶ K')
  (hc : (F.mapHomologicalComplex (.up ℕ)).map f ≫ b.hom = a.hom ≫ r)

abbrev source := RefinedInferred.Comparison.source
  (GeometricComparison.ExactHomology.ExactHomologyComparison.naturality F (.up ℕ) a b f r hc i).symm hg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobal.Comparison
