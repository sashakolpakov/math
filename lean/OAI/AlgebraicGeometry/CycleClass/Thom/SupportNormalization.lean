import Mathlib.AlgebraicGeometry.OrderOfVanishing
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Local
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType

/-! # Support Normalization -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportNormalization.Constructions

noncomputable section

/-! Finiteness of the actual normalization of each support stalk. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [CharZero k]
  {X : Scheme.{u}} [IsIntegral X]

theorem finite_stalk_normalization (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let x' : U := ⟨x, X.affineCover.covers x⟩
  let : Nonempty U := ⟨x'⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let : Algebra.FiniteType k Γ(X, U) :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of k)).inv (f.appLE ⊤ U le_top)).mpr
        (f.finiteType_appLE (isAffineOpen_top _) hU le_top)
  let M := (hU.primeIdealOf x').asIdeal.primeCompl
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  let := hU.isLocalization_stalk x'
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let := functionField_isScalarTower X U x'
  exact Thom.Finite.Normalization.Constructions.finite_integralClosure_localization
    k Γ(X, U) (X.presheaf.stalk x) X.functionField M

/-- Normalization of the local ring at a codimension-one point is a finite
Dedekind algebra, even when that point is singular. -/
theorem stalk_normalization_isDedekind (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : Order.coheight x = 1) :
    IsDedekindDomain (integralClosure (X.presheaf.stalk x) X.functionField) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    krullDimLE_of_coheight_le hx.le
  let := finite_stalk_normalization f x
  exact Normalization.Local.Constructions.isDedekindDomain_integralClosure
    (X.presheaf.stalk x) X.functionField

/-- The order of a regular germ equals the quotient length on its actual
normalization, rather than on an assumed regular replacement. -/
theorem ord_eq_stalk_normalization_length (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : Order.coheight x = 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    Ring.ord (X.presheaf.stalk x) a = Module.length (X.presheaf.stalk x)
      ((integralClosure (X.presheaf.stalk x) X.functionField) ⧸
        Ideal.span {algebraMap (X.presheaf.stalk x)
          (integralClosure (X.presheaf.stalk x) X.functionField) a}) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    krullDimLE_of_coheight_le hx.le
  let := finite_stalk_normalization f x
  let : IsFractionRing (integralClosure (X.presheaf.stalk x) X.functionField)
      X.functionField := integralClosure.isFractionRing_of_finite_extension
        X.functionField X.functionField
  exact Thom.Finite.Colength.Constructions.ord_eq_length_birational_extension
    (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField)
      X.functionField a ha

/-- The same comparison computes the geometric integer order of an arbitrary
nonzero quotient of germs, including its poles. -/
theorem ord_fraction_eq_normalization_lengths [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : Order.coheight x = 1)
    (a b : X.presheaf.stalk x) (ha : a ≠ 0) (hb : b ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b) x =
      ((Module.length (X.presheaf.stalk x)
        ((integralClosure (X.presheaf.stalk x) X.functionField) ⧸
          Ideal.span {algebraMap (X.presheaf.stalk x)
            (integralClosure (X.presheaf.stalk x) X.functionField) a})).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        ((integralClosure (X.presheaf.stalk x) X.functionField) ⧸
          Ideal.span {algebraMap (X.presheaf.stalk x)
            (integralClosure (X.presheaf.stalk x) X.functionField) b})).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← ord_eq_stalk_normalization_length f x hx a ha,
    ← ord_eq_stalk_normalization_length f x hx b hb,
    Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change WithZero.log (Ring.ordFrac (X.presheaf.stalk x)
    (algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b)) = _
  rw [map_div₀, Ring.ordFrac_eq_ord _ ha, Ring.ordFrac_eq_ord _ hb,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero ha)
      (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hb)
      (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hb))).symm]
  exact WithZero.log_div (by simp) (by simp)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportNormalization.Constructions
