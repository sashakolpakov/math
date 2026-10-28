import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Presentation
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface

/-! # Local Neighbors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM

noncomputable section

/-! Instantiate local neighbor transport on the actual TateComparison source,
Albanese map, and Neron extension of its integral raw operator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Presentation.CM.Hecke
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "eta" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
local notation "jq" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.localFieldEmbedding j)
abbrev localSource := (Over.pullback eta).obj (AlbaneseMapCompatibility.CM.integralSource D hg j hcop)
local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM.localSource D hg j hcop

def rawEnd (f : D.EndK) : (A).ExtendingEndomorphism :=
  Presentation.CM.Hecke.extendingEndomorphism A (EndomorphismComparison.CM.integralEquiv (A).variety.scheme f)

theorem rawEnd_algebraic_generic (f : D.EndK) :
    (rawEnd D hg j hcop f).generic = EndomorphismComparison.CM.integralEquiv (A).variety.scheme f :=
  Presentation.CM.Hecke.extendingEndomorphism_generic A (EndomorphismComparison.CM.integralEquiv (A).variety.scheme f)

theorem rawEnd_generic (f : D.EndK) : ExtendingPointAction.CM.genericEnd A (rawEnd D hg j hcop f) = f :=
  (EndomorphismComparison.CM.integralEquiv (A).variety.scheme).symm_apply_apply f

variable (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q]))

def originalPoint (x : T ⟶ X) : (Over.map jq).obj T ⟶ D.space :=
  BaseChangeEvaluation.CM.pointsEquiv jq T D.space (x ≫ (AlbaneseMapCompatibility.CM.genericSourceIso D hg j hcop).hom)

def genericAlbaneseMap : X ⟶ (Geometric.ComparisonSpecialization.CM.localGroup A).X :=
  (Over.pullback eta).map (AlbaneseMapCompatibility.CM.integralMap D hg j hcop)

def genericGroupPoint (z : (Over.map jq).obj T ⟶ D.space) :
    Additive ((Over.map jq).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) :=
  Additive.ofMul (z ≫ AlbaneseMapCompatibility.CM.genericMap D hg j hcop)

theorem genericGroupPoint_eq (z : (Over.map jq).obj T ⟶ D.space) :
    genericGroupPoint D hg j hcop T z = D.aTotalPoint hg z :=
  congrArg Additive.ofMul (congrArg (z ≫ ·) (AlbaneseMapCompatibility.CM.genericMap_eq D hg j hcop))

theorem rawPoint_evaluation (f : D.EndK)
    (x : Additive ((Over.map jq).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X)) :
    PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map jq).obj T) (ExtendingPointAction.CM.genericEnd A (rawEnd D hg j hcop f)) x =
      D.endPoint f x := by
  rw [rawEnd_generic]
  apply Additive.toMul.injective
  exact AbelianScheme.TateComparison.End.endSchemeMap_points D.albaneseGroup.X f ((Over.map jq).obj T) x.toMul

theorem source_local_neighbor_formula (f : D.EndK) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map jq).obj T ⟶ D.space))
    (h : ModelNeighborFormula.CM.PointEquation A (AlbaneseMapCompatibility.CM.nativeSource D hg j hcop) T
      (D.albaneseMap hg) (D.endPoint f) x y Nx Ny) :
    ModelNeighborFormula.CM.LocalEquation A (AlbaneseMapCompatibility.CM.nativeSource D hg j hcop) T
      (rawEnd D hg j hcop f) x y Nx Ny := by
  apply ModelNeighborFormula.CM.localEquation_of_genericEquation
    A (AlbaneseMapCompatibility.CM.nativeSource D hg j hcop) T (rawEnd D hg j hcop f) x y Nx Ny
  exact ModelNeighborFormula.CM.genericEquation_of_named_point_formula
    A (AlbaneseMapCompatibility.CM.nativeSource D hg j hcop) T (rawEnd D hg j hcop f)
    (D.albaneseMap hg) (AlbaneseMapCompatibility.CM.genericMap_eq D hg j hcop) (D.endPoint f)
    (rawPoint_evaluation D hg j hcop T f) x y Nx Ny h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM
