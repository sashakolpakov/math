import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticEquationPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EquationImages
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionTargetIdentification

/-! # Arithmetic Group Equation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticGroupEquation.CM.ImageCompatibility

/-! Prove the arithmetic image identity before instantiating the PEL
model. Replacing a proved-equal target comparison preserves the actual
source reduction map, so both formulas use the identical source point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {X : Over S} [IsProper X.hom] (a : X ⟶ G.scheme)
  (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
  (w : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k)
  (br : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q) ⟶ S)
  (wr : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q) ≫ t = br)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "eta" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "A" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM.ComparisonModel.model K _ _ q _ jq S g G k t w
local notation "M" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM.sourceMap K _ _ q _ jq S g G X a k t w
local notation "redM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM.reductionMap G a red t br wr
local notation "bR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.integralBase V
local notation "cL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q)
local notation "wL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.generic_square V
local notation "rho" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM.geometricResidue (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM.geometricResidueIso V)
local notation "gk" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.geometricBase (q := q)
local notation "uk" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.residueBase V
local notation "Uk" => Over.mk gk
local notation "eR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.testIso V

local instance : IsProper (M).integralSource.hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom t))

variable (e : ((G.pullback t).pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).scheme ≅
    (G.pullback br).scheme)
  (he : (ReductionComparisonModel.CM.reductionMap G a (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) t br wr).targetIso.hom = e.hom)
  (U₀ : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K))
  (p : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj (Over.mk (EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))) ⟶ U₀)

local notation "aligned" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionTargetIdentification.CM.replaceTarget G a red t br redM e he

theorem image_eq (z : U₀ ⟶ (Over.pullback k).obj X) :
    Source.EquationImages.CM.image A M bR cL wL rho Uk eR
      (CommGrp.mk (G.pullback br).scheme) (aligned).sourceIso ((Over.pullback br).map a) U₀ p z =
    Additive.ofMul (ArithmeticEquationPoints.CM.point G a k t w br wr V (p ≫ z) ≫
      (Over.pullback br).map a) := rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticGroupEquation.CM.ImageCompatibility

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticGroupEquation.CM

/-! Arithmetic source reduction with an independently specified target
group. The actual target group and map are retained throughout the
equation; only the arithmetic source points are identified. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {X : Over S} [IsProper X.hom] (a : X ⟶ G.scheme)
  (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
  (w : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k)
  (br : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q) ⟶ S)
  (wr : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q) ≫ t = br)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "eta" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "A" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM.ComparisonModel.model K _ _ q _ jq S g G k t w
local notation "M" => @OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM.sourceMap K _ _ q _ jq S g G X a k t w
local notation "redM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM.reductionMap G a red t br wr
local notation "bR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.integralBase V
local notation "cL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q)
local notation "wL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.generic_square V
local notation "rho" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM.geometricResidue (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM.geometricResidueIso V)
local notation "gk" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.geometricBase (q := q)
local notation "uk" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.residueBase V
local notation "Uk" => Over.mk gk
local notation "eR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.testIso V

local instance : IsProper (M).integralSource.hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom t))

variable (H : CommGrp (Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q))))
  (e : (@BaseChangeSquare.CM.ComparisonModel.model K _ _ q _ jq S g G k t w).specialFiber.scheme ≅ H.X)
  [hmon : IsMonHom e.hom]
  (b : (Over.pullback br).obj X ⟶ H.X)
  (U₀ : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K))
  (p : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj (Over.mk (EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))) ⟶ U₀)

def image (z : U₀ ⟶ (Over.pullback k).obj X) : Additive (Uk ⟶ H.X) :=
  Additive.ofMul (ArithmeticEquationPoints.CM.point G a k t w br wr V (p ≫ z) ≫ b)

theorem image_eq (z : U₀ ⟶ (Over.pullback k).obj X) :
    Source.EquationImages.CM.image A M bR cL wL rho Uk eR H (redM).sourceIso b U₀ p z =
      image G a k t w br wr V H b U₀ p z := rfl

def Input (f : (A).ExtendingEndomorphism)
    (x y : U₀ ⟶ (Over.pullback k).obj X) (Nx Ny : Multiset (U₀ ⟶ (Over.pullback k).obj X)) : Prop :=
  @Source.EquationImages.CM.Equation K _ _ q _ jq A M _
    V.carrier L _ _ _ _ _ _ bR cL wL (AlgebraicClosure (ZMod q)) _ rho Uk eR
    H e hmon _ (redM).sourceIso b U₀ p f x y Nx Ny

def Output (g' : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd H.X)
    (x y : U₀ ⟶ (Over.pullback k).obj X) (Nx Ny : Multiset (U₀ ⟶ (Over.pullback k).obj X)) : Prop :=
  Source.EquationImages.CM.ImageEquation (PointEvaluation.CM.action H Uk g')
    (image G a k t w br wr V H b U₀ p) x y Nx Ny

theorem equation (f : (A).ExtendingEndomorphism) (g' : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd H.X)
    (hf : SpecialEndEvaluation.CM.TransportedSpecialization.algebraicSpecialization A H e f.generic = g')
    (x y : U₀ ⟶ (Over.pullback k).obj X) (Nx Ny : Multiset (U₀ ⟶ (Over.pullback k).obj X))
    (h : Input G a k t w br wr V H e b U₀ p f x y Nx Ny) :
    Output G a k t w br wr V H b U₀ p g' x y Nx Ny :=
  @Source.EquationImages.CM.equation_with_images K _ _ q _ jq A M _
    V.carrier L _ _ _ _ _ _ bR cL wL (AlgebraicClosure (ZMod q)) _ rho Uk eR H e hmon _
    (redM).sourceIso b U₀ p f g' hf (image G a k t w br wr V H b U₀ p)
    (image_eq G a k t w br wr V H b U₀ p) x y Nx Ny h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticGroupEquation.CM

end

end OAI
