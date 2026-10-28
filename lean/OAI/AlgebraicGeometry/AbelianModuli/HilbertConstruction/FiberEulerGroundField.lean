import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.EquivalentDimensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic

/-! # Fiber Euler Ground Field -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberEulerGroundField

noncomputable section

/-! The geometric fiber Euler function is exactly genuine Euler characteristic over the residue field itself. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def lineBundleFieldSectionDimension {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) : ℕ :=
  Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf)

theorem fiberEulerCharacteristic_eq_groundField
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (x : S) :
    Geometric.FiberEuler.fiberEulerCharacteristic f L x =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)).sheaf := by
  apply finsum_congr
  intro q
  let e : S.residueField x ≃+* Γ(Spec (S.residueField x), ⊤) :=
    (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.symm
  let M := (L.pullback (f.fiberι x)).sheaf
  let H := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom q).obj M
  have h₁ := Scalar.EquivalentDimensions.restrictScalars_finrank_of_ringEquiv e H
  have h₂ := (CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso e.toRingHom
    (f.fiberToSpecResidueField x).appTop.hom M q).toLinearEquiv.finrank_eq
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ)) (h₁.symm.trans h₂)

theorem properFlat_groundFieldFiberEuler_isLocallyConstant
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) :
    IsLocallyConstant (fun x : S =>
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)).sheaf) := by
  have hfun : (fun x : S =>
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)).sheaf) =
        Geometric.FiberEuler.fiberEulerCharacteristic f L := by
    funext x
    exact (fiberEulerCharacteristic_eq_groundField f L x).symm
  rw [hfun]
  exact ProperFlat.FiberEuler.properFlat_fiberEuler_isLocallyConstant f L

theorem properFlat_groundFieldSectionDimension_isLocallyConstant
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    (hH : ∀ (x : S) q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf (q + 1))) :
    IsLocallyConstant (fun x : S =>
      (lineBundleFieldSectionDimension (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)) : ℤ)) := by
  have hfun : (fun x : S =>
      (lineBundleFieldSectionDimension (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)) : ℤ)) =
      fun x => CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)).sheaf := by
    funext x
    apply (CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
      (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)).sheaf _).symm
    intro q
    have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap (f.fiberToSpecResidueField x)) (q + 1)).obj (L.pullback (f.fiberι x)).sheaf) := hH x q
    exact ModuleCat.isZero_of_subsingleton _
  rw [hfun]
  exact properFlat_groundFieldFiberEuler_isLocallyConstant f L

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberEulerGroundField
