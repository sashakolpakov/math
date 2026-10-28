import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothPresheafCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CechSheafification
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothCechProduct

/-! # Algebraic Smooth Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AlgebraicSmoothCech

noncomputable section

/-! The very algebraic-to-smooth native Čech map used by the cup
product comparison is a quasi-isomorphism on projective covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

private theorem totalMap_comp {C : Type*} [Category* C]
    (N : SimplicialObject (FormalCoproduct.{0} C))
    {K L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    CechCoefficient.Naturality.Total.totalMap N (f ≫ g) =
      CechCoefficient.Naturality.Total.totalMap N f ≫ CechCoefficient.Naturality.Total.totalMap N g := by
  unfold CechCoefficient.Naturality.Total.totalMap CechCoefficient.Naturality.Total.bicomplexMap
  erw [Functor.map_comp, HomologicalComplex₂.total.map_comp]
  rfl

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

theorem original_map_quasiIso (n : ℕ)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left] :
    QuasiIso (CechCoefficient.Naturality.Total.totalMap
      (FormalCoproduct.mk (Fin (n + 2))
        (fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)).cech
      (AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.presheafSmoothCochainMap X)) := by
  let U := fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i
  let N := (FormalCoproduct.mk (Fin (n + 2)) U).cech
  have hi : IsIso (CechCoefficient.Naturality.Total.totalMap N
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X)) :=
    Affine.CechSheafification.cech_unit_isIso X U
      (AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity.embeddedProjectiveCoordinateCover_affine (n + 1) X f)
  have hq : QuasiIso (CechCoefficient.Naturality.Total.totalMap N
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicSheafToSmoothPresheafMap X)) :=
    SmoothPresheafCech.map_quasiIso X n f
  have hu : QuasiIso (CechCoefficient.Naturality.Total.totalMap N
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X)) := quasiIso_of_isIso _
  have hc : QuasiIso (CechCoefficient.Naturality.Total.totalMap N
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicPresheafSheafificationUnit X) ≫
        CechCoefficient.Naturality.Total.totalMap N (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicSheafToSmoothPresheafMap X)) :=
    quasiIso_comp _ _ (hφ := hu) (hφ' := hq)
  rw [← totalMap_comp, AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicSheafToSmoothPresheafMap_normalization] at hc
  exact hc

theorem native_map_quasiIso (n : ℕ)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left] :
    QuasiIso (AlgebraicSmoothCechProduct.totalMap X
      (FormalCoproduct.mk (Fin (n + 2))
        (fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)).cech) := by
  let N := (FormalCoproduct.mk (Fin (n + 2))
    (fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)).cech
  let e := ((FormalCoproduct.cochainComplexFunctor N).mapHomologicalComplex (.up ℕ)).mapIso
    (GeometricComparison.SheafFormsAdapter.FormsAdapter.presheafComplexIso X).symm
  have hi : IsIso (CechCoefficient.Naturality.Total.totalMap N
      (GeometricComparison.SheafFormsAdapter.FormsAdapter.presheafComplexIso X).inv) :=
    (HomologicalComplex₂.total.mapIso e (.up ℕ)).isIso_hom
  have hq := original_map_quasiIso X n f
  change QuasiIso (CechCoefficient.Naturality.Total.totalMap N
    ((GeometricComparison.SheafFormsAdapter.FormsAdapter.presheafComplexIso X).inv ≫ AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.presheafSmoothCochainMap X))
  rw [totalMap_comp]
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := hq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AlgebraicSmoothCech
