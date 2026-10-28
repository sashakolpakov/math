import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralFirstThreeSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalRegularity

/-! # Three Cech Regularity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechRegularity.IntegralFirstThreeCechRegularity

noncomputable section

/-! The actual integral three-term coordinate Čech total is regular for every regular base coefficient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite ZeroObject

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsSeparated X.hom] [Smooth X.hom] {ι : Type} (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (r : R) (hr : IsRegular r)

local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U

include hU hr in
theorem ordinary_regular (n p : ℕ) (hn : n ≤ 2) :
    IsSMulRegular (((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).X p) r := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  change IsSMulRegular (∏ᶜ (fun t : Fin (p + 1) → ι =>
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op (∏ᶜ (U ∘ t)))) : ModuleCat R) r
  apply Module.TotalRegularity.ModuleTotalRegularity.product
  intro t
  exact GeometricComparison.Smooth.IntegralFirstThreeSections.SmoothIntegralFirstThreeSections.forms_regular R X (∏ᶜ (U ∘ t))
    (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p t) n hn r hr

include hU hr in
theorem component_regular (n p : ℕ) : IsSMulRegular (((B).X n).X p) r := by
  rcases n with _ | (_ | (_ | n))
  · exact ordinary_regular R X U hU r hr 0 p (by omega)
  · exact ordinary_regular R X U hU r hr 1 p (by omega)
  · exact ordinary_regular R X U hU r hr 2 p (by omega)
  · let F := AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℕ) p
    have hz : IsZero (F.obj (0 : X.left.Opensᵒᵖ ⥤ ModuleCat R)) :=
      F.map_isZero (isZero_zero _)
    have hs : Subsingleton (F.obj (0 : X.left.Opensᵒᵖ ⥤ ModuleCat R)) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    intro x y _
    exact hs.elim x y

include hU hr in
theorem total_regular (n : ℕ) : IsSMulRegular (((B).total (.up ℕ)).X n) r :=
  Module.TotalRegularity.ModuleTotalRegularity.total B r (component_regular R X U hU r hr) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechRegularity.IntegralFirstThreeCechRegularity
