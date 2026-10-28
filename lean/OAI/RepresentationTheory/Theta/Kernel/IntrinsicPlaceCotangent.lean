import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceGraph
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodProjection
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphProjector
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison

/-! # Intrinsic Place Cotangent -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent.Intrinsic

/-! The native place projection is exactly its cotangent position
projection: its apparent lower-left phase block vanishes by the full
Gaussian and geometric identities. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlacePairing.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphProjector.Intrinsic

theorem standard_pairing_real {I : Type} [Fintype I] (x y : (I ⊕ I) → ℝ) :
    Adelic.DataTheta.standardPairing (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) = ((Adelic.DataTheta.standardPairing x y : ℝ) : ℂ) := by
  simp only [Adelic.DataTheta.standardPairing,Complex.ofReal_sum,Complex.ofReal_sub,Complex.ofReal_mul]

theorem phase_pairing_standard {I k : Type} [Fintype I] [Field k] (x y : (I ⊕ I) → k) :
    IntrinsicGraphProjector.Intrinsic.phasePairing x y = Adelic.DataTheta.standardPairing x y := (Finset.sum_sub_distrib _ _).symm

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem complex_place_pairing_balance (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (v : Fin A.places) (x y : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    Adelic.DataTheta.standardPairing (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) x) y =
      Adelic.DataTheta.standardPairing x (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) y) := by
  let E := IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v)
  let f := (IntrinsicSymplecticComparison.Intrinsic.pairingBilinear ℂ (Adelic.BallGeometryData.FrameIndex A)).compl₁₂ E LinearMap.id
  let g := (IntrinsicSymplecticComparison.Intrinsic.pairingBilinear ℂ (Adelic.BallGeometryData.FrameIndex A)).compl₁₂ LinearMap.id E
  have he : f = g := by
    apply IntrinsicRealComplexification.Intrinsic.complexLinear_ext_real
    intro u
    apply IntrinsicRealComplexification.Intrinsic.complexLinear_ext_real
    intro w
    change Adelic.DataTheta.standardPairing (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) (fun i => (u i : ℂ)))
      (fun i => (w i : ℂ)) =
        Adelic.DataTheta.standardPairing (fun i => (u i : ℂ))
          (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) (fun i => (w i : ℂ)))
    rw [IntrinsicRealComplexification.Intrinsic.complexifiedLinear_real,IntrinsicRealComplexification.Intrinsic.complexifiedLinear_real,standard_pairing_real,standard_pairing_real]
    exact congrArg Complex.ofReal (IntrinsicPlacePairing.Intrinsic.native_place_pairing_balance B hC v u w)
  exact congrArg (fun T => T x y) he

theorem native_complex_place_cotangent {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
    {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
    (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)
    (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) x =
      Sum.elim ((IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B v).mulVec (fun i => x (.inl i)))
        ((IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B v)ᵀ.mulVec (fun i => x (.inr i))) := by
  apply IntrinsicGraphProjector.Intrinsic.graph_projector_cotangent _ _ (B.period z).matrix
  · intro u w
    rw [phase_pairing_standard,phase_pairing_standard]
    exact complex_place_pairing_balance B hC v u w
  · intro u i
    exact congrFun (IntrinsicPositionProjection.Intrinsic.complex_place_positions B hC v u) i
  · exact IntrinsicPlaceGraph.Intrinsic.native_place_graph B hC hG v z
  · exact IntrinsicPeriodProjection.Intrinsic.native_period_projection B hO v z

end RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent.IntrinsicReal

/-! The exact place-projection identity in the real native phase
coordinates, obtained from the proved complex Gaussian graph identity. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}

theorem native_real_place_cotangent (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)
    (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) :
    IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v x =
      Sum.elim (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v (fun i => x (.inl i)))
        ((LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v))ᵀ.mulVec (fun i => x (.inr i))) := by
  have he := Intrinsic.native_complex_place_cotangent B hC hG hO v z (fun i => (x i : ℂ))
  rw [IntrinsicRealComplexification.Intrinsic.complexifiedLinear_real] at he
  funext i
  cases i with
  | inl i =>
    apply Complex.ofReal_injective
    exact (congrFun he (.inl i)).trans
      (congrFun (IntrinsicRealComplexification.Intrinsic.complexifiedLinear_real (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v) (fun j => x (.inl j))) i)
  | inr i =>
    apply Complex.ofReal_injective
    exact (congrFun he (.inr i)).trans
      (Complex.ofRealHom.map_mulVec (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v))ᵀ
        (fun j => x (.inr j)) i).symm

end RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent.IntrinsicReal

end

end OAI
