import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ComplexMaps
import Mathlib.Algebra.Homology.Functor

/-! # De Rham Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamRestriction

noncomputable section

/-! The actual coefficient de Rham presheaf restrictions agree with native chart algebra maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {U V : X.left.Opens} (h : V ≤ U)

def map :
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) U).mapHomologicalComplex (.up ℕ)).obj
      (Global.DeRhamCoefficientComplex.complex p k X) ⟶
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) V).mapHomologicalComplex (.up ℕ)).obj
      (Global.DeRhamCoefficientComplex.complex p k X) :=
  (HomologicalComplex.asFunctor (Global.DeRhamCoefficientComplex.complex p k X)).map (homOfLE h).op

omit [Fintype k] [CharP k p] in
theorem chart_naturality : DeRhamRestriction.map p k X h ≫ (DeRham.Comparison.deRhamIso p k X V).hom =
    (DeRham.Comparison.deRhamIso p k X U).hom ≫
      EtaleZero.ComplexMaps.deRhamMap p k
        ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U))
        ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op V)) (SectionRestriction.algHom k X h) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamRestriction
