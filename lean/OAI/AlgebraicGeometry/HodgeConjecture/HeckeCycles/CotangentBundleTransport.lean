import OAI.RepresentationTheory.Hecke.RadialDilation.Prerequisites
import OAI.RepresentationTheory.Theta.Adelic.Prerequisites

/-! # Cotangent Bundle Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CotangentBundleTransport.CM

/-! Full CotangentBundle interface transport. The two bundle calculi are distinct
structures; every operation and every law is copied explicitly. Neither
direction assumes the requested determinant or cotangent conclusion. -/

universe u v

def toSupplier {B : Type u} {A : Type v} [CommSemiring B] [CommGroup A]
    (C : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.BundleCalculus B A) : Geometry.ComplexBall.CotangentBundle.BundleCalculus B A where
  line := C.line
  rank := C.rank
  dual := C.dual
  det := C.det
  shortExact := C.shortExact
  rank_line := C.rank_line
  rank_dual := C.rank_dual
  dual_involutive := C.dual_involutive
  det_line := C.det_line
  det_sum := C.det_sum
  det_tensor := C.det_tensor
  det_dual := C.det_dual
  rank_exact := C.rank_exact
  det_exact := C.det_exact

def toConsumer {B : Type u} {A : Type v} [CommSemiring B] [CommGroup A]
    (C : Geometry.ComplexBall.CotangentBundle.BundleCalculus B A) : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.BundleCalculus B A where
  line := C.line
  rank := C.rank
  dual := C.dual
  det := C.det
  shortExact := C.shortExact
  rank_line := C.rank_line
  rank_dual := C.rank_dual
  dual_involutive := C.dual_involutive
  det_line := C.det_line
  det_sum := C.det_sum
  det_tensor := C.det_tensor
  det_dual := C.det_dual
  rank_exact := C.rank_exact
  det_exact := C.det_exact

theorem supplier_consumer {B : Type u} {A : Type v} [CommSemiring B] [CommGroup A]
    (C : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.BundleCalculus B A) : toConsumer (toSupplier C) = C := rfl

theorem consumer_supplier {B : Type u} {A : Type v} [CommSemiring B] [CommGroup A]
    (C : Geometry.ComplexBall.CotangentBundle.BundleCalculus B A) : toSupplier (toConsumer C) = C := rfl

theorem full_input_iff :
    RepresentationTheory.Theta.Adelic.Prerequisites.CotangentBundleInput.{u, v} ↔
      ∀ (B : Type u) (A : Type v) [CommSemiring B] [CommGroup A],
        @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _ := by
  constructor
  · intro h B A _ _ C n L Vμ Q P K ℱ hV hP hQ hSU hM hK hdec
    exact h (toSupplier C) n L Vμ Q P K ℱ hV hP hQ hSU hM hK hdec
  · intro h B A _ _ C n L Vμ Q P K ℱ hV hP hQ hSU hM hK hdec
    exact h B A (toConsumer C) n L Vμ Q P K ℱ hV hP hQ hSU hM hK hdec

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CotangentBundleTransport.CM
