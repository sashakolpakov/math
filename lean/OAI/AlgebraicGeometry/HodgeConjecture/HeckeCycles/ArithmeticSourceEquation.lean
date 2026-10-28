import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EquationImages
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionTargetIdentification

/-! # Arithmetic Source Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticSourceEquation.CM

noncomputable section

/-! The arithmetic base-change construction supplies the entire
specialization equation map. Its commuting source and Albanese square
is proved before instantiating the native arithmetic model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {X : Over S} [IsProper X.hom] (a : X ⟶ G.scheme)
  (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
  (w : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k)
  (br : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q) ⟶ S)
  (wr : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q) ≫ t = br)

local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "A" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM.ComparisonModel.model K _ _ q _ jq S g G k t w
local notation "M" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM.sourceMap K _ _ q _ jq S g G X a k t w
local notation "redM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM.reductionMap G a red t br wr

abbrev targetGroup : CommGrp (Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q))) := CommGrp.mk (G.pullback br).scheme

variable (e : ((G.pullback t).pullback
    (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).scheme ≅ (G.pullback br).scheme)
  (he : (ReductionComparisonModel.CM.reductionMap G a (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) t br wr).targetIso = e)

local notation "aligned" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionTargetIdentification.CM.replaceTarget G a red t br redM e
  (congrArg Iso.hom he)

local instance : IsProper (M).integralSource.hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom t))

variable {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q]) (c : Spec (.of L) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q])
  (wc : c ≫ NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)
  {κ : Type} [Field κ] (res : R →+* κ)
  (U : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q)))
  (test : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).obj U ≅ ValuativePoints.CM.specialTest bR res)

/- `PLift` packages the fully proved function as data, so its exact
dependent type is inferred from the checked specialization theorem. -/
def transport := PLift.up (
  @Source.EquationImages.CM.Transported.equation_from_special K _ _ q _ jq A M
    (inferInstanceAs (IsProper (pullback.snd X.hom t)))
    R L _ _ _ _ _ _ bR c wc κ _ res U test (targetGroup (q := q) G br) e
    (aligned).target_group _ (aligned).sourceIso ((Over.pullback br).map a)
    (aligned).compatible)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticSourceEquation.CM
