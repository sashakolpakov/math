import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineOpenFormsUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter
import OAI.AlgebraicGeometry.Comparison.Betti.ConcreteCech
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.CechForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Naturality

/-! # Cech Sheafification -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CechSheafification

noncomputable section

/-! Sheafifying actual rational differential forms induces an
isomorphism on the native Čech total of a separated affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)

theorem unit_app_isIso (U : X.left.Opens) (hU : IsAffineOpen U) (p : ℕ) :
    IsIso (((AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X).f p).app (op U)) := by
  change IsIso ((toSheafify (Opens.grothendieckTopology X.left)
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.formPresheaf X p)).app (op U))
  exact GeometricComparison.SheafificationUnit.SheafificationUnitTransfer.of_iso (Opens.grothendieckTopology X.left)
    (GeometricComparison.SheafFormsAdapter.FormsAdapter.formPresheafIso X p) (op U)
    (GeometricComparison.Intrinsic.AffineOpenFormsUnit.IntrinsicAffineOpenFormsUnit.on_open ℂ X U hU p)

variable [IsSeparated X.hom] {ι : Type} (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

include hU in
theorem cech_unit_component_isIso (p a : ℕ) :
    IsIso (((CechCoefficient.Naturality.Total.bicomplexMap (FormalCoproduct.mk ι U).cech
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X)).f p).f a) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  change IsIso (CategoryTheory.Limits.Pi.map (fun t : Fin (a + 1) → ι =>
    ((AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X).f p).app
      (op (∏ᶜ fun k : Fin (a + 1) => U (t k)))))
  have (t : Fin (a + 1) → ι) : IsIso
      (((AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X).f p).app
        (op (∏ᶜ fun k : Fin (a + 1) => U (t k)))) :=
    unit_app_isIso X _ (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU a t) p
  infer_instance

include hU in
theorem cech_unit_isIso :
    IsIso (CechCoefficient.Naturality.Total.totalMap (FormalCoproduct.mk ι U).cech
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X)) := by
  let φ := CechCoefficient.Naturality.Total.bicomplexMap (FormalCoproduct.mk ι U).cech
    (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X)
  have (p a : ℕ) : IsIso ((φ.f p).f a) := cech_unit_component_isIso X U hU p a
  have (p : ℕ) : IsIso (φ.f p) := HomologicalComplex.Hom.isIso_of_components (φ.f p)
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  exact (HomologicalComplex₂.total.mapIso (asIso φ) (.up ℕ)).isIso_hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CechSheafification
