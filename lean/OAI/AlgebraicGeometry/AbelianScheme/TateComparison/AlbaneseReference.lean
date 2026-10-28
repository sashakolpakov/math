import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Albanese
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality

/-! # Albanese Reference -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Construction supplies a projective Albanese reference for each actual
component. The given Albanese candidate maps onto this reference. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem AlbaneseReference.albanese_comparison_points_surjective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsCommMonObj G]
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ G) (b : X.toOver ⟶ B.toOver)
    (hb : PELModuli.IntegralModel.Albanese.IsAlbaneseMap X x₀ B b)
    (φ : G ⟶ B.toOver) [IsMonHom φ] (hφ : a ≫ φ = b) :
    Function.Surjective (fun z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G => z ≫ φ) := by
  let F := IsMonHom.monoidHom φ (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
  have hr : Subgroup.closure (Albanese.Construction.WordPoints.differencePointImage X B b) ≤ F.range := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨p, rfl⟩
    refine ⟨((p ≫ fst X.toOver X.toOver) ≫ a) / ((p ≫ snd X.toOver X.toOver) ≫ a), ?_⟩
    change (((p ≫ fst X.toOver X.toOver) ≫ a) / ((p ≫ snd X.toOver X.toOver) ≫ a)) ≫ φ = _
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, hφ]
    simp only [Albanese.Construction.ImageWords.differenceMap, GrpObj.comp_div, Category.assoc, hφ]
  rw [PELModuli.IntegralModel.Albanese.albanese_generates X x₀ B b hb] at hr
  exact MonoidHom.range_eq_top.mp (le_antisymm le_top hr)

theorem AlbaneseReference.albanese_comparison_surjective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsCommMonObj G] [IsProper G.hom]
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ G) (b : X.toOver ⟶ B.toOver)
    (hb : PELModuli.IntegralModel.Albanese.IsAlbaneseMap X x₀ B b)
    (φ : G ⟶ B.toOver) [IsMonHom φ] (hφ : a ≫ φ = b) : Surjective φ.left := by
  have : IsProper B.toOver.hom := B.variety.presentation.projective.isProper
  have : IsProper (φ.left ≫ B.toOver.hom) := φ.w.symm ▸ inferInstanceAs (IsProper G.hom)
  have : IsProper φ.left := IsProper.of_comp φ.left B.toOver.hom
  have : LocallyOfFiniteType B.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType B.variety.structureMap)
  have hfull : Set.range (𝟙 B.toOver : B.toOver ⟶ B.toOver).left ⊆ Set.range φ.left := by
    apply Albanese.Construction.ReducedFactor.range_subset_closed_of_points B.toOver B.toOver (𝟙 B.toOver)
      ⟨Set.range φ.left, φ.left.isClosedMap.isClosed_range⟩
    intro y
    obtain ⟨z, hz⟩ := AlbaneseReference.albanese_comparison_points_surjective X x₀ G B a b hb φ hφ y
    exact ⟨z.left (IsLocalRing.closedPoint ℂ), congrArg
      (fun r : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ B.toOver => r.left (IsLocalRing.closedPoint ℂ)) hz⟩
  exact ⟨fun y => hfull ⟨y, rfl⟩⟩

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def Data.SphericalPELAlbaneseData.complexComponentVariety (j : Fin D.componentCount) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := by
  have : Smooth (D.components.S j).hom := (hg.componentGeometry j).1
  have : IsProper (D.components.S j).hom := (hg.componentGeometry j).2.1
  have : GeometricallyConnected (D.components.S j).hom := (hg.componentGeometry j).2.2.2
  let C := D.components.complexSurface D.complexPoint j
  have : Smooth C.hom := inferInstanceAs (Smooth (pullback.snd (D.components.S j).hom D.complexPoint))
  have : IsProper C.hom := inferInstanceAs (IsProper (pullback.snd (D.components.S j).hom D.complexPoint))
  have : GeometricallyConnected C.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd (D.components.S j).hom D.complexPoint))
  have : ConnectedSpace C.left := GeometricallyConnected.connectedSpace_of_subsingleton C.hom
  refine ⟨{ carrier := C.left, structureMap := C.hom, projective := ?_, smooth := inferInstance }, ?_⟩
  · exact AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
      ((hg.componentGeometry j).2.2.1.some.baseChange D.complexPoint)
  · exact ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral C.hom

def Data.SphericalPELAlbaneseData.componentReferenceAlbanese (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (j : Fin D.componentCount) : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  (hConstruction (D.complexComponentVariety hg j).presentation (D.components.complexBasePoint D.complexPoint j)).choose

def Data.SphericalPELAlbaneseData.componentReferenceMap (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (j : Fin D.componentCount) :
    D.components.complexSurface D.complexPoint j ⟶ (D.componentReferenceAlbanese hg hConstruction j).toOver :=
  (hConstruction (D.complexComponentVariety hg j).presentation
    (D.components.complexBasePoint D.complexPoint j)).choose_spec.choose

theorem Data.SphericalPELAlbaneseData.componentReference_isAlbanese (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (j : Fin D.componentCount) :
    PELModuli.IntegralModel.Albanese.IsAlbaneseMap (D.complexComponentVariety hg j).presentation
      (D.components.complexBasePoint D.complexPoint j) (D.componentReferenceAlbanese hg hConstruction j)
      (D.componentReferenceMap hg hConstruction j) :=
  (hConstruction (D.complexComponentVariety hg j).presentation
    (D.components.complexBasePoint D.complexPoint j)).choose_spec.choose_spec

theorem Data.SphericalPELAlbaneseData.componentReference_comparison_exists (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (j : Fin D.componentCount) :
    ∃ φ : (D.components.complexAbelian D.complexPoint j).X ⟶ (D.componentReferenceAlbanese hg hConstruction j).toOver,
      IsMonHom φ ∧ D.components.complexMap D.complexPoint j ≫ φ = D.componentReferenceMap hg hConstruction j ∧
        Surjective φ.left := by
  obtain ⟨φ, ⟨hφ, hf⟩, _⟩ := (hg.albanese j).2 (D.componentReferenceAlbanese hg hConstruction j)
    (D.componentReferenceMap hg hConstruction j) (D.componentReference_isAlbanese hg hConstruction j).1
  have : IsMonHom φ := hφ
  have : IsProper (D.components.A j).X.hom := (hg.abelianGeometry j).2.1
  have : IsProper (D.components.complexAbelian D.complexPoint j).X.hom :=
    inferInstanceAs (IsProper (pullback.snd (D.components.A j).X.hom D.complexPoint))
  exact ⟨φ, hφ, hf, AlbaneseReference.albanese_comparison_surjective (D.complexComponentVariety hg j).presentation
    (D.components.complexBasePoint D.complexPoint j) (D.components.complexAbelian D.complexPoint j).X
    (D.componentReferenceAlbanese hg hConstruction j) (D.components.complexMap D.complexPoint j)
    (D.componentReferenceMap hg hConstruction j) (D.componentReference_isAlbanese hg hConstruction j) φ hf⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
