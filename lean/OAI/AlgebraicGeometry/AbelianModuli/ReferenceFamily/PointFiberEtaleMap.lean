import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorRestriction
import Mathlib.RingTheory.RingHom.Etale

/-! # Point Fiber Etale Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberEtaleMap

noncomputable section

section

/-! A specified etale coordinate map gives a linear map of
coefficient derivations in the fixed fibers. It is determined uniquely
by the literal tensor restriction on the original regular functions. -/

open scoped TensorProduct

variable (k R A D : Type) [Field k] [CommRing R] [CommRing A] [CommRing D]
    [Algebra k R] [Algebra k A] [Algebra k D] [Algebra R k] [Algebra R A] [Algebra R D]
    [IsScalarTower k R k] [IsScalarTower k R A] [IsScalarTower k R D]

local instance pointFiberEtaleMap_sourceRing : CommRing (k ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := A)

local instance pointFiberEtaleMap_targetRing : CommRing (k ⊗[R] D) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := D)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def pointFiberEtaleDerivationMap (q : A →ₐ[R] D) (hq : q.toRingHom.Etale) :
    Derivation k A (k ⊗[R] A) →ₗ[k] Derivation k D (k ⊗[R] D) := by
  let : Algebra A D := q.toRingHom.toAlgebra
  let : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq (fun r => (q.commutes r).symm)
  let : IsScalarTower k A D :=
    IsScalarTower.of_algebraMap_eq (fun c => ((q.restrictScalars k).commutes c).symm)
  have : Algebra.Etale A D := hq
  exact PointFiberTensorRestriction.pointFiberTensorDerivationRestriction k R A D

theorem pointFiberEtaleDerivationMap_apply (q : A →ₐ[R] D) (hq : q.toRingHom.Etale)
    (d : Derivation k A (k ⊗[R] A)) (a : A) :
    pointFiberEtaleDerivationMap k R A D q hq d (q a) =
      Algebra.TensorProduct.map (AlgHom.id k k) q (d a) := by
  let : Algebra A D := q.toRingHom.toAlgebra
  let : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq (fun r => (q.commutes r).symm)
  let : IsScalarTower k A D :=
    IsScalarTower.of_algebraMap_eq (fun c => ((q.restrictScalars k).commutes c).symm)
  have : Algebra.Etale A D := hq
  exact PointFiberTensorRestriction.pointFiberTensorDerivationRestriction_algebraMap k R A D d a

theorem pointFiberEtaleDerivationMap_unique (q : A →ₐ[R] D) (hq : q.toRingHom.Etale)
    (d : Derivation k A (k ⊗[R] A)) (e : Derivation k D (k ⊗[R] D))
    (h : ∀ a, e (q a) = Algebra.TensorProduct.map (AlgHom.id k k) q (d a)) :
    e = pointFiberEtaleDerivationMap k R A D q hq d := by
  let : Algebra A D := q.toRingHom.toAlgebra
  let : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq (fun r => (q.commutes r).symm)
  let : IsScalarTower k A D :=
    IsScalarTower.of_algebraMap_eq (fun c => ((q.restrictScalars k).commutes c).symm)
  have : Algebra.Etale A D := hq
  exact PointFiberTensorRestriction.pointFiberTensorDerivationRestriction_unique k R A D d e h

end

/-! Fixed-fiber coefficient derivation maps respect equal maps,
identity maps, and successive etale restrictions. -/

open scoped TensorProduct

variable (k R A D : Type) [Field k] [CommRing R] [CommRing A] [CommRing D]
    [Algebra k R] [Algebra k A] [Algebra k D] [Algebra R k] [Algebra R A] [Algebra R D]
    [IsScalarTower k R k] [IsScalarTower k R A] [IsScalarTower k R D]

theorem pointFiberEtaleDerivationMap_congr (q r : A →ₐ[R] D)
    (hq : q.toRingHom.Etale) (hr : r.toRingHom.Etale) (h : q = r) :
    pointFiberEtaleDerivationMap k R A D q hq = pointFiberEtaleDerivationMap k R A D r hr := by
  subst r
  rfl

omit [Algebra k D] [Algebra R D] [IsScalarTower k R D] in
theorem pointFiberEtaleDerivationMap_id (h : (AlgHom.id R A).toRingHom.Etale) :
    pointFiberEtaleDerivationMap k R A A (AlgHom.id R A) h = LinearMap.id := by
  apply LinearMap.ext
  intro d
  apply Eq.symm
  apply pointFiberEtaleDerivationMap_unique k R A A (AlgHom.id R A) h
  intro a
  rw [Algebra.TensorProduct.map_id]
  rfl

variable (F : Type) [CommRing F] [Algebra k F] [Algebra R F] [IsScalarTower k R F]

theorem pointFiberEtaleDerivationMap_comp (q : A →ₐ[R] D) (r : D →ₐ[R] F)
    (hq : q.toRingHom.Etale) (hr : r.toRingHom.Etale) (hrq : (r.comp q).toRingHom.Etale) :
    pointFiberEtaleDerivationMap k R A F (r.comp q) hrq =
      (pointFiberEtaleDerivationMap k R D F r hr).comp (pointFiberEtaleDerivationMap k R A D q hq) := by
  apply LinearMap.ext
  intro d
  apply Eq.symm
  apply pointFiberEtaleDerivationMap_unique k R A F (r.comp q) hrq
  intro a
  change pointFiberEtaleDerivationMap k R D F r hr
      (pointFiberEtaleDerivationMap k R A D q hq d) (r (q a)) = _
  rw [pointFiberEtaleDerivationMap_apply, pointFiberEtaleDerivationMap_apply,
    Algebra.TensorProduct.map_id_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberEtaleMap
