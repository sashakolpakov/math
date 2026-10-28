import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Isogeny Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyPeriods.AbelianIntrinsicAdapter

noncomputable section

/-! An actual isogeny between the original complex abelian schemes
induces isomorphisms of complex tangent spaces and rational periods.
The maps are the genuine period lifts, with no inverse isogeny input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def nativeIsogenyMap : (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA).toOver ⟶ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB).toOver :=
  (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f.hom ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv

instance nativeIsogenyMap_isMonHom : IsMonHom (nativeIsogenyMap A B PA PB f) :=
  inferInstanceAs (IsMonHom ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f.hom ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv))

instance nativeIsogenyMap_isFinite : IsFinite (nativeIsogenyMap A B PA PB f).left := by
  let : IsIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom.left :=
    inferInstanceAs (IsIso (((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA)).hom))
  let : IsIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv.left :=
    inferInstanceAs (IsIso (((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB)).inv))
  exact inferInstanceAs (IsFinite ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom.left ≫ f.hom.left ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv.left))

theorem nativeIsogeny_complex_finrank :
    Module.finrank ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) = Module.finrank ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) := by
  have ha : Module.finrank ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) = g :=
    (Module.finrank_fin_fun ℂ).trans (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A)
  have hb : Module.finrank ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) = g :=
    (Module.finrank_fin_fun ℂ).trans (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq B)
  exact ha.trans hb.symm

theorem nativeIsogeny_rational_finrank :
    Module.finrank ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) = Module.finrank ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) := by
  have ha : Module.finrank ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) = 2 * g :=
    (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)).trans (congrArg (fun n : ℕ => 2 * n) (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A))
  have hb : Module.finrank ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) = 2 * g :=
    (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)).trans (congrArg (fun n : ℕ => 2 * n) (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq B))
  exact ha.trans hb.symm

def nativeIsogenyComplexEquiv : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ≃ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) :=
  (Maps.IntrinsicLinearMaps.linearLift (nativeIsogenyMap A B PA PB f)).linearEquivOfInjective
    (Finite.ComplexFibers.NativeLinearMaps.linearLift_injective_of_isFinite _) (nativeIsogeny_complex_finrank A B PA PB)

def nativeIsogenyRationalEquiv : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) :=
  (IntegralMaps.IntrinsicLinearMaps.rationalLift (nativeIsogenyMap A B PA PB f)).linearEquivOfInjective
    (Finite.ComplexFibers.NativeLinearMaps.rationalLift_injective_of_isFinite _) (nativeIsogeny_rational_finrank A B PA PB)

theorem nativeIsogenyComplexEquiv_apply (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    nativeIsogenyComplexEquiv A B PA PB f v = Maps.IntrinsicLinearMaps.linearLift (nativeIsogenyMap A B PA PB f) v := rfl

theorem nativeIsogenyRationalEquiv_apply (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    nativeIsogenyRationalEquiv A B PA PB f v = IntegralMaps.IntrinsicLinearMaps.rationalLift (nativeIsogenyMap A B PA PB f) v := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyPeriods.AbelianIntrinsicAdapter
