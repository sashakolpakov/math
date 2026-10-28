import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FunctionDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalPrincipalDivisor

/-! # Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Divisor

noncomputable section

/-! Functions algebraic over the base's function field have zero order
at every normal point above its generic point. In relative dimension one
this kills their entire principal-divisor pushforward. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberFields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem ord_eq_zero {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (x : X) (hx : f x = genericPoint Y) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (g : X.functionField) (hg : g ≠ 0) :
    letI := Generic.FiberFields.fieldAlgebra f hη
    IsAlgebraic Y.functionField g → X.ord g x = 0 := by
  let := Generic.FiberFields.fieldAlgebra f hη
  intro ha
  by_cases hxone : coheight x = 1
  · let := Generic.FiberFields.stalkAlgebra f x hx
    let := Generic.FiberFields.stalkTower f hη x hx
    let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hxone.le
    obtain ⟨a, hau, hag⟩ := FunctionDivisor.algebraic_isUnit_integer
      Y.functionField (X.presheaf.stalk x) X.functionField g hg ha
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hxone]
    change WithZero.log (Ring.ordFrac (X.presheaf.stalk x) g) = 0
    rw [← hag, Ring.ordFrac_of_isUnit hau, WithZero.log_one]
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hxone g

theorem principalDivisor_pushforward {K : Type} [Field K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : X.functionField) (hg : g ≠ 0) :
    letI := Generic.FiberFields.fieldAlgebra f hη
    IsAlgebraic Y.functionField g → CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X g) = 0 := by
  let := Generic.FiberFields.fieldAlgebra f hη
  intro ha
  ext y
  apply BirationalPrincipalDivisor.pointPushforward_eq_zero_of_degrees
  intro x hx _
  by_contra hdeg
  have hxone : coheight x = 1 := by
    by_contra h
    apply hx
    rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one h, Int.cast_zero]
  have hxy := Generic.FiberDimension.image_eq_genericPoint f gY hdim x hxone hdeg
  let := hNormal x
  exact hx (by rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, ord_eq_zero f hη x hxy g hg ha, Int.cast_zero])

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Divisor
