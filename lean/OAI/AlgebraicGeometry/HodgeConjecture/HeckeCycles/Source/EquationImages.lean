import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedSpecialEquation

/-! # Equation Images -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EquationImages.CM.Transported

/-! Transport the reduced source equation through the actual source
and group identifications, retaining the same algebraic specialization
and every specialized neighbor, including multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : ComparisonModel.CM.SourceMap A) [IsProper M.integralSource.hom]
  {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q]) (c : Spec (.of L) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q])
  (w : c ≫ NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)
  {k : Type} [Field k] (res : R →+* k)
  (U : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q)))
  (test : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).obj U ≅ ValuativePoints.CM.specialTest bR res)
  (H : CommGrp (Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q)))) (e : A.specialFiber.scheme ≅ H.X)
  [IsMonHom e.hom] {Y : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q))}
  (s : SourceSpecialEquation.CM.specialSource A M ≅ Y) (b : Y ⟶ H.X)

local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "T" => Over.mk c
local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localSource A M
local notation "px" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM.specialPoint A M bR c w res U test
local notation "pn" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM.specialNeighbor A M bR c w res U test

def Equation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  TransportedSpecialEquation.CM.Equation A H e U s b f (px x) (px y)
    (Nx.map pn) (Ny.map pn)

theorem equation_from_special
    (hs : (Over.pullback red).map M.integralMap ≫ e.hom = s.hom ≫ b)
    (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : SourceSpecialEquation.CM.SpecialEquation A M bR c w res U test f x y Nx Ny) :
    Equation A M bR c w res U test H e s b f x y Nx Ny := by
  apply TransportedSpecialEquation.CM.equation_from_integral A H e U s
    ((Over.pullback red).map M.integralMap) b hs f (px x) (px y) (Nx.map pn) (Ny.map pn)
  rw [SpecialEndEvaluation.CM.specialIntegralEnd_eq]
  simp only [SourceSpecialEquation.CM.SpecialEquation, Multiset.map_map, Function.comp_def] at h ⊢
  exact h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EquationImages.CM.Transported

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EquationImages.CM

/-! Normalize the transported source equation before instantiating the
arithmetic model. The same specialized-neighbor image is used for both
source points and every original neighbor, retaining multiplicities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM

def ImageEquation {S G : Type} [AddCommGroup G] (u : G → G) (a : S → G)
    (x y : S) (Nx Ny : Multiset S) : Prop :=
  u (a x - a y) = (Nx.map a).sum - (Ny.map a).sum

theorem imageEquation_congr {S G : Type} [AddCommGroup G]
    (u v : G → G) (hu : u = v) (a b : S → G) (hab : a = b)
    (x y : S) (Nx Ny : Multiset S) (h : ImageEquation u a x y Nx Ny) :
    ImageEquation v b x y Nx Ny := by
  subst v
  subst b
  exact h

theorem change_image {S G : Type} [AddCommGroup G]
    (u v : G → G) (hu : u = v) (a b : S → G) (hab : a = b)
    (x y : S) (Nx Ny : Multiset S)
    (h : u (a x - a y) = (Nx.map a).sum - (Ny.map a).sum) :
    v (b x - b y) = (Nx.map b).sum - (Ny.map b).sum := by
  subst v
  subst b
  exact h

theorem evaluated_points {S G : Type} [AddCommGroup G]
    (u : G → G) (a : S → G) (x y : S) (Nx Ny : Multiset S)
    (sx sy : G) (rx ry : Multiset G)
    (hx : a x = sx) (hy : a y = sy) (hNx : Nx.map a = rx) (hNy : Ny.map a = ry)
    (h : ImageEquation u a x y Nx Ny) : u (sx - sy) = rx.sum - ry.sum := by
  unfold ImageEquation at h
  rw [hx, hy, hNx, hNy] at h
  exact h

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : ComparisonModel.CM.SourceMap A) [IsProper M.integralSource.hom]
  {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q]) (c : Spec (.of L) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q])
  (w : c ≫ NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)
  {k : Type} [Field k] (res : R →+* k)
  (U : Over (Spec (.of (ZMod q))))
  (test : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).obj U ≅ ValuativePoints.CM.specialTest bR res)
  (H : CommGrp (Over (Spec (.of (ZMod q))))) (e : A.specialFiber.scheme ≅ H.X)
  [IsMonHom e.hom] {Y : Over (Spec (.of (ZMod q)))}
  (s : SourceSpecialEquation.CM.specialSource A M ≅ Y) (b : Y ⟶ H.X)

local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "T" => Over.mk c
local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localSource A M
local notation "px" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM.specialPoint A M bR c w res U test
local notation "pn" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM.specialNeighbor A M bR c w res U test

variable (U₀ : Over (Spec (.of K))) (p : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj (Over.mk c) ⟶ U₀)

def image (z : U₀ ⟶ M.genericSource) : Additive (U ⟶ H.X) :=
  Additive.ofMul ((SourceSpecialEquation.CM.specialNeighbor A M bR c w res U test (p ≫ z) ≫ s.hom) ≫ b)

def specializedAction (f : A.ExtendingEndomorphism) :
    Additive (U ⟶ H.X) → Additive (U ⟶ H.X) :=
  PointEvaluation.CM.action H U
    (SpecialEndEvaluation.CM.TransportedSpecialization.algebraicSpecialization A H e f.generic)

def Equation (f : A.ExtendingEndomorphism) (x y : U₀ ⟶ M.genericSource)
    (Nx Ny : Multiset (U₀ ⟶ M.genericSource)) : Prop :=
  ImageEquation (specializedAction A U H e f)
    (image A M bR c w res U test H s b U₀ p) x y Nx Ny

theorem equation_from_transported (f : A.ExtendingEndomorphism) (x y : U₀ ⟶ M.genericSource)
    (Nx Ny : Multiset (U₀ ⟶ M.genericSource))
    (h : Transported.Equation A M bR c w res U test H e s b f
      (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso (p ≫ x)) (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso (p ≫ y))
      (Nx.map (p ≫ ·)) (Ny.map (p ≫ ·))) :
    Equation A M bR c w res U test H e s b U₀ p f x y Nx Ny := by
  unfold Equation ImageEquation image specializedAction
  simpa only [Transported.Equation, TransportedSpecialEquation.CM.Equation,
    SourceSpecialEquation.CM.specialPoint, SourceSpecialEquation.CM.specialNeighbor, EvaluatedFormula.CM.reducedRawNeighbor,
    Multiset.map_map, Function.comp_def] using h

theorem equation_with_images (f : A.ExtendingEndomorphism) (g : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd H.X)
    (hg : SpecialEndEvaluation.CM.TransportedSpecialization.algebraicSpecialization A H e f.generic = g)
    (a : (U₀ ⟶ M.genericSource) → Additive (U ⟶ H.X))
    (ha : ∀ z, image A M bR c w res U test H s b U₀ p z = a z)
    (x y : U₀ ⟶ M.genericSource) (Nx Ny : Multiset (U₀ ⟶ M.genericSource))
    (h : Equation A M bR c w res U test H e s b U₀ p f x y Nx Ny) :
    ImageEquation (PointEvaluation.CM.action H U g) a x y Nx Ny :=
  change_image _ _ (congrArg (fun z => ⇑(PointEvaluation.CM.action H U z)) hg)
    _ a (funext ha) x y Nx Ny h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EquationImages.CM

end

end OAI
