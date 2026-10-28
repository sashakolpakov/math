import OAI.RepresentationTheory.Theta.Adelic.TotallyRealData
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles
import Mathlib.Topology.Instances.RealVectorSpace
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest

/-! # Minkowski Coordinates Position -/

namespace OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition

noncomputable section

section

/-! The specified real completions give actual Minkowski coordinates.
The integral-basis coordinates extend the rational coordinates exactly. -/

open scoped Classical _root_.NumberField

open _root_.NumberField OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def realInfiniteEquiv : InfiniteAdeleRing F ≃+* (Fin A.places → ℝ) :=
  (RingEquiv.piCongrLeft (fun v : InfinitePlace F => v.Completion) A.enumerate).symm.trans
    (RingEquiv.piCongrRight A.real)

def realInfiniteHomeomorph : InfiniteAdeleRing F ≃ₜ (Fin A.places → ℝ) :=
  (Homeomorph.piCongrLeft (Y := fun v : InfinitePlace F => v.Completion)
    A.enumerate).symm.trans
    (Homeomorph.piCongrRight (fun v =>
      { toEquiv := (A.real v).toEquiv
        continuous_toFun := A.real_continuous v
        continuous_invFun := A.real_inverse_continuous v }))

theorem realInfiniteEquiv_continuous : Continuous (realInfiniteEquiv A) :=
  (realInfiniteHomeomorph A).continuous

theorem realInfiniteEquiv_inverse_continuous : Continuous (realInfiniteEquiv A).symm :=
  (realInfiniteHomeomorph A).symm.continuous

theorem realInfiniteEquiv_apply (x : InfiniteAdeleRing F) (v : Fin A.places) :
    realInfiniteEquiv A x v = A.real v (x (A.enumerate v)) := rfl

def realMixedAddEquiv : (Fin A.places → ℝ) ≃+ mixedEmbedding.mixedSpace F :=
  (realInfiniteEquiv A).symm.toAddEquiv.trans
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv

def realMixedEquiv : (Fin A.places → ℝ) ≃L[ℝ] mixedEmbedding.mixedSpace F :=
  (realMixedAddEquiv A).toRealLinearEquiv
    ((Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).continuous.comp
      (realInfiniteEquiv_inverse_continuous A))
    ((realInfiniteEquiv_continuous A).comp
      (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).symm.continuous)

def realScalarCoordinates :
    (Fin A.places → ℝ) ≃L[ℝ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) :=
  (realMixedEquiv A).trans
    (mixedEmbedding.latticeBasis F).equivFun.toContinuousLinearEquiv

theorem realMixedEquiv_rational (q : F) :
    realMixedEquiv A (fun v => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) q)) =
      mixedEmbedding F q := by
  have h : (fun v => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) q)) =
      realInfiniteEquiv A (algebraMap F (InfiniteAdeleRing F) q) := rfl
  change InfiniteAdeleRing.ringEquiv_mixedSpace F ((realInfiniteEquiv A).symm _) = _
  rw [h, RingEquiv.symm_apply_apply]
  exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F (x := q)).symm

theorem realScalarCoordinates_rational (q : F) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    realScalarCoordinates A (fun v =>
      A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) q)) i =
        ((integralBasis F).repr q i : ℝ) := by
  change (mixedEmbedding.latticeBasis F).repr (realMixedEquiv A _) i = _
  rw [realMixedEquiv_rational, mixedEmbedding.latticeBasis_repr_apply]

end

section

/-! Rational and real Schrödinger position coordinates, indexed by the
actual Hodge frame. -/

open scoped Classical _root_.NumberField

open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TotallyRealData

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def scalarIndexEquiv : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ Fin A.places :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, ← Module.finrank_eq_card_basis (integralBasis F)]
    exact TotallyRealData.degree_eq_places A)

def frameCoefficientEquiv :
    BallGeometryData.FrameIndex A ≃ (Fin (3 * m) × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :=
  ((scalarIndexEquiv A).symm.prodCongr finProdFinEquiv).trans (Equiv.prodComm _ _)

def flattenCoordinates (R : Type*) [Semiring R] :
    (Fin (3 * m) → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → R) ≃ₗ[R] (BallGeometryData.FrameIndex A → R) :=
  (LinearEquiv.curry R R _ _).symm.trans
    (LinearEquiv.funCongrLeft R R (frameCoefficientEquiv A))

theorem flattenCoordinates_apply {R : Type*} [Semiring R]
    (x : Fin (3 * m) → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → R) (i : BallGeometryData.FrameIndex A) :
    flattenCoordinates A R x i = x (finProdFinEquiv i.2) ((scalarIndexEquiv A).symm i.1) := rfl

def rationalPositionCoordinates : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (BallGeometryData.FrameIndex A → ℚ) :=
  (LinearEquiv.piCongrRight (fun _ : Fin (3 * m) => (integralBasis F).equivFun)).trans
    (flattenCoordinates A ℚ)

def transposePositions : BallGeometryData.RealPositions A ≃ₗ[ℝ] (Fin (3 * m) → Fin A.places → ℝ) where
  toFun x i v := x v i
  invFun x v i := x i v
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def realPositionCoordinates : BallGeometryData.RealPositions A ≃L[ℝ] (BallGeometryData.FrameIndex A → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv ((transposePositions A).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin (3 * m) =>
      (realScalarCoordinates A).toLinearEquiv)).trans (flattenCoordinates A ℝ)))

theorem rationalPositionCoordinates_apply (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) (i : BallGeometryData.FrameIndex A) :
    rationalPositionCoordinates A x i =
      (integralBasis F).repr (x (finProdFinEquiv i.2)) ((scalarIndexEquiv A).symm i.1) := rfl

theorem realPositionCoordinates_apply (x : BallGeometryData.RealPositions A) (i : BallGeometryData.FrameIndex A) :
    realPositionCoordinates A x i = realScalarCoordinates A
      (fun v => x v (finProdFinEquiv i.2)) ((scalarIndexEquiv A).symm i.1) := rfl

theorem realPositionCoordinates_rational (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) (i : BallGeometryData.FrameIndex A) :
    realPositionCoordinates A (BallGeometryData.archPositions A x) i =
      (rationalPositionCoordinates A x i : ℝ) :=
  realScalarCoordinates_rational A _ _

end

/-! Minkowski position lattices in the exact rationally normalized
coordinates used by the geometric Siegel period. -/

open scoped Classical _root_.NumberField

open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

theorem continuousLinearEquiv_map_discrete {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) (L : Submodule ℤ V) [DiscreteTopology L] :
    DiscreteTopology (L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap) := by
  have hm (x : L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap) : e.symm x.val ∈ L := by
    obtain ⟨y, hy, hxy⟩ := x.property
    have he : e y = x.val := hxy
    rw [← he, ContinuousLinearEquiv.symm_apply_apply]
    exact hy
  let i : L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap → L := fun x => ⟨e.symm x.val, hm x⟩
  have hi : Continuous i := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  apply DiscreteTopology.of_continuous_injective hi
  intro x y h
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg Subtype.val h

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def mixedPositionCoordinates :
    (Fin (3 * m) → mixedEmbedding.mixedSpace F) ≃L[ℝ] (BallGeometryData.FrameIndex A → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    ((LinearEquiv.piCongrRight (fun _ : Fin (3 * m) => (mixedEmbedding.latticeBasis F).equivFun)).trans
      (flattenCoordinates A ℝ))

theorem mixedPositionCoordinates_apply (x : Fin (3 * m) → mixedEmbedding.mixedSpace F) (i : BallGeometryData.FrameIndex A) :
    mixedPositionCoordinates A x i =
      (mixedEmbedding.latticeBasis F).repr (x (finProdFinEquiv i.2)) ((scalarIndexEquiv A).symm i.1) := rfl

theorem mixedPositionCoordinates_rational (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    mixedPositionCoordinates A (Weil.AdelicSplitting.ThetaTest.Construction.mixedRationalPosition F (3 * m) x) =
      fun i => (rationalPositionCoordinates A x i : ℝ) := by
  funext i
  rw [mixedPositionCoordinates_apply, rationalPositionCoordinates_apply]
  exact mixedEmbedding.latticeBasis_repr_apply F _ _

def coordinateSupportLattice (r : F) : Submodule ℤ (BallGeometryData.FrameIndex A → ℝ) :=
  (Weil.AdelicSplitting.ThetaTest.Construction.mixedPositionLattice F (3 * m) r).map
    ((mixedPositionCoordinates A).toLinearEquiv.restrictScalars ℤ).toLinearMap

theorem coordinateSupportLattice_discrete (r : F) (hr : r ≠ 0) :
    DiscreteTopology (coordinateSupportLattice A r) := by
  let : DiscreteTopology (Weil.AdelicSplitting.ThetaTest.Construction.mixedPositionLattice F (3 * m) r) :=
    Weil.AdelicSplitting.ThetaTest.Construction.mixedPositionLattice_discrete F (3 * m) r hr
  exact continuousLinearEquiv_map_discrete (mixedPositionCoordinates A) _

theorem coordinateSupportLattice_rational (r : F) (hr : r ≠ 0)
    (l : coordinateSupportLattice A r) :
    ∃ x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m), (fun i => (rationalPositionCoordinates A x i : ℝ)) = l.val := by
  obtain ⟨y, hy, hyl⟩ := l.property
  change ∀ i, ∃ b : 𝓞 F, mixedEmbedding F (b : F) = mixedEmbedding F r * y i at hy
  choose b hb using hy
  let x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) := fun i => r⁻¹ * (b i : F)
  have hinv : mixedEmbedding F r⁻¹ * mixedEmbedding F r = 1 := by
    rw [← map_mul (mixedEmbedding F), inv_mul_cancel₀ hr, map_one]
  have hx : Weil.AdelicSplitting.ThetaTest.Construction.mixedRationalPosition F (3 * m) x = y := by
    funext i
    change mixedEmbedding F (r⁻¹ * (b i : F)) = y i
    rw [map_mul, hb, ← mul_assoc, hinv, one_mul]
  refine ⟨x, ?_⟩
  rw [← mixedPositionCoordinates_rational, hx]
  exact hyl

end

end OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
