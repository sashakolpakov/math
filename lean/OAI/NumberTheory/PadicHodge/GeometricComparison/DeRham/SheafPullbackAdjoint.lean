import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAdjunction

/-! # Sheaf Pullback Adjoint -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafPullbackAdjoint

noncomputable section

/-! The actual native sheaf-form pullback has the originally defined direct-image map as its coefficientwise adjoint. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

theorem sheafPullback_adjoint (n : ℕ) :
    (Int.imageAdjunction f).homEquiv _ _ ((Int.sheafPullback f).f n) = (Int.sheafDirectImage f).f n :=
  (ComplexAdjunction.ComplexAdjunctionComponents.homEquiv_f (Int.imageAdjunction f) (.up ℕ)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) (Int.sheafPullback f) n).symm.trans
      (congrArg (fun k => k.f n) (((Int.imageComplexAdjunction f).homEquiv _ _).apply_symm_apply (Int.sheafDirectImage f)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafPullbackAdjoint
