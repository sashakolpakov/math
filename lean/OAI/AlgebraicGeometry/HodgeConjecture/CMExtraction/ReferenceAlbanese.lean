import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Total

/-! # Reference Albanese -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReferenceAlbanese.Intrinsic

noncomputable section

/-! Projective Albanese references are constructed from the full Construction and HodgeComparison
inputs. Their maps to the native component groups come from IntegralModel universality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem projective_albanese_reference
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ V.toOver)
    (A : CommGrp (Over Foundations.Scheme.ProjectiveSpace.complexBase)) (a : V.toOver ⟶ A.X)
    (ha : ∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : V.toOver ⟶ B.toOver), x₀ ≫ b = 1 →
      ∃! ψ : A.X ⟶ B.toOver, IsMonHom ψ ∧ a ≫ ψ = b) :
    ∃ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : V.toOver ⟶ B.toOver)
      (ψ : A.X ⟶ B.toOver)
      (e : B.variety.rationalCohomology 1 ≃ₗ[ℚ] V.rationalCohomology 1),
      IsMonHom ψ ∧ a ≫ ψ = b ∧
      e.toLinearMap = PELModuli.IntegralModel.Product.bettiPullbackQ b 1 ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (Mem.canonicalH1 hHodgeDecomposition V.presentation)
        (Mem.canonicalH1 hHodgeDecomposition B.variety.presentation) e.symm.toLinearMap := by
  let : ConnectedSpace V.presentation.carrier := inferInstanceAs (ConnectedSpace V.carrier)
  obtain ⟨B, b, hb⟩ := hConstruction V.presentation x₀
  obtain ⟨ψ, hψ, _⟩ := ha B b hb.1
  obtain ⟨HB, HV, e, hB, hV, he, _, hback⟩ :=
    hHodgeComparison V x₀ B b ((PELModuli.IntegralModel.AlbaneseCohomology.e08_isAlbanese_iff V x₀ B b).mpr hb)
  refine ⟨B, b, ψ, e, hψ.1, hψ.2, he, ?_⟩
  intro x hx
  rw [Naturality.canonicalH1_integral_holomorphic] at hx ⊢
  rw [← hV.1] at hx
  rw [← hB.1]
  exact hback x hx

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def singleBaseComponentVariety (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := by
  let : Smooth (D.pel.components.S j).hom := (hg.componentGeometry j).1
  let : IsProper (D.pel.components.S j).hom := (hg.componentGeometry j).2.1
  let : GeometricallyConnected (D.pel.components.S j).hom := (hg.componentGeometry j).2.2.2
  let C := D.pel.components.complexSurface D.pel.complexPoint j
  let : Smooth C.hom := by dsimp [C]; infer_instance
  let : IsProper C.hom := by dsimp [C]; infer_instance
  let : GeometricallyConnected C.hom := by dsimp [C]; infer_instance
  exact ⟨{ carrier := C.left
           structureMap := C.hom
           projective := RepresentationTheory.Theta.Geometric.ComponentVarieties.RelativeProjective.complexProjectivePresentation
             (Classical.choice (hg.componentGeometry j).2.2.1) D.pel.complexPoint
           smooth := inferInstance }, RepresentationTheory.Theta.Geometric.Components.smooth_proper_connected_integral C⟩

theorem native_component_reference
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount) :
    ∃ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (b : (singleBaseComponentVariety D hg j).toOver ⟶ B.toOver)
      (ψ : (D.pel.components.complexAbelian D.pel.complexPoint j).X ⟶ B.toOver)
      (e : B.variety.rationalCohomology 1 ≃ₗ[ℚ]
        (singleBaseComponentVariety D hg j).rationalCohomology 1),
      IsMonHom ψ ∧ D.pel.components.complexMap D.pel.complexPoint j ≫ ψ = b ∧
      e.toLinearMap = PELModuli.IntegralModel.Product.bettiPullbackQ b 1 ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (Mem.canonicalH1 hHodgeDecomposition (singleBaseComponentVariety D hg j).presentation)
        (Mem.canonicalH1 hHodgeDecomposition B.variety.presentation) e.symm.toLinearMap := by
  exact projective_albanese_reference hHodgeDecomposition hConstruction hHodgeComparison (singleBaseComponentVariety D hg j)
    (D.pel.components.complexBasePoint D.pel.complexPoint j)
    (D.pel.components.complexAbelian D.pel.complexPoint j)
    (D.pel.components.complexMap D.pel.complexPoint j) (hg.albanese j).2

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReferenceAlbanese.Intrinsic
