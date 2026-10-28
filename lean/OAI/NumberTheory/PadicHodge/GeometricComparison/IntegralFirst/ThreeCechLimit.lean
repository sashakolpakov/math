import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientLimit

/-! # Three Cech Limit -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechLimit.IntegralFirstThreeCechLimit

/-! Integral three-term Cech cohomology identifies with the categorical
inverse limit of its original shifted principal quotients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [IsNoetherianRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
  (r : R) (hr : IsRegular r) [IsAdicComplete (Ideal.span {r}) R]

local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex R X U

def iso (i : ℕ) (hi : i ≤ 1) : (C).homology i ≅ limit (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram R C r i) :=
  (ThreeCechCompletion.IntegralFirstThreeCechCompletion.equiv R X U hU hcover r hr i hi).toModuleIso ≪≫
    CochainQuotientLimit.PrincipalCochainQuotient.compatibleLimitIso R C r i

omit [Finite ι] in
theorem eval (i : ℕ) (hi : i ≤ 1) (x : (C).homology i) (n : ℕ) :
    limit.π (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram R C r i) (op n) ((iso R X U hU hcover r hr i hi).hom x) =
      CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r (n + 1) i x :=
  (CochainQuotientLimit.PrincipalCochainQuotient.compatibleLimitIso_eval R C r i
    (ThreeCechCompletion.IntegralFirstThreeCechCompletion.equiv R X U hU hcover r hr i hi x) n).trans
      (ThreeCechCompletion.IntegralFirstThreeCechCompletion.equiv_eval R X U hU hcover r hr i hi x (n + 1))

end NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechLimit.IntegralFirstThreeCechLimit

namespace NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechLimit.IntegralFirstThreeCechLimitCoordinates

/-! The Cech completion isomorphism has the original quotient reduction
as each categorical limit projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [IsNoetherianRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type} (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
  (r : R) (hr : IsRegular r) [IsAdicComplete (Ideal.span {r}) R]

local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex R X U

theorem hom_π (i : ℕ) (hi : i ≤ 1) (n : ℕ) :
    (IntegralFirstThreeCechLimit.iso R X U hU hcover r hr i hi).hom ≫
      limit.π (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram R C r i) (op n) =
        ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r (n + 1) i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact IntegralFirstThreeCechLimit.eval R X U hU hcover r hr i hi x n

end NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechLimit.IntegralFirstThreeCechLimitCoordinates

end

end OAI
