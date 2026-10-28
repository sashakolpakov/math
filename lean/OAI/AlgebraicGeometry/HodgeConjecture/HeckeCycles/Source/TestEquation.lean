import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula

/-! # Test Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TestEquation.CM

noncomputable section

/-! An actual evaluated equation over the number-field test is
transported through the canonical test isomorphism and then through the
original source comparison, retaining both neighbor multisets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceLocalEquation.CM.Reference
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM

theorem mapped_neighbor_formula {S : Scheme} (G : CommGrp (Over S))
    {T U X : Over S} (p : T ⟶ U) (a : X ⟶ G.X) (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : U ⟶ X) (Nx Ny : Multiset (U ⟶ X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt G U f (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt G T f (Additive.ofMul ((p ≫ x) ≫ a) - Additive.ofMul ((p ≫ y) ≫ a)) =
      ((Nx.map (p ≫ ·)).map (fun z => Additive.ofMul (z ≫ a))).sum -
        ((Ny.map (p ≫ ·)).map (fun z => Additive.ofMul (z ≫ a))).sum := by
  simpa only [Multiset.map_map, Function.comp_def] using
    PointSpecializationFormula.CM.Test.neighbor_formula G p a f x y Nx Ny h

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def PointEquation (U : Over (Spec (.of K))) (f : D.EndK) (x y : U ⟶ D.space)
    (Nx Ny : Multiset (U ⟶ D.space)) : Prop :=
  PointSpecializationFormula.CM.Points.evaluateAt D.albaneseGroup U f
    (Additive.ofMul (x ≫ D.albaneseMap hg) - Additive.ofMul (y ≫ D.albaneseMap hg)) =
    (Nx.map (fun z => Additive.ofMul (z ≫ D.albaneseMap hg))).sum -
      (Ny.map (fun z => Additive.ofMul (z ≫ D.albaneseMap hg))).sum

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator) (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q]))
  (U : Over (Spec (.of K)))
  (e : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (QadicModelMap.CM.localFieldEmbedding j))).obj T ≅ U)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "M" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM.nativeSource D hg j hcop

theorem local_equation_from_test (f : D.EndK) (x y : U ⟶ D.space)
    (Nx Ny : Multiset (U ⟶ D.space)) (h : PointEquation D hg U f x y Nx Ny) :
    ReferenceLocalEquation.CM.Reference.LocalOriginalEquation A M T (LocalNeighbors.CM.rawEnd D hg j hcop f)
      (e.hom ≫ x) (e.hom ≫ y) (Nx.map (e.hom ≫ ·)) (Ny.map (e.hom ≫ ·)) := by
  apply ReferenceEquation.CM.Reference.local_equation_of_original_evaluation D hg j hcop T f
  exact mapped_neighbor_formula D.albaneseGroup e.hom (D.albaneseMap hg) f x y Nx Ny h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TestEquation.CM
