import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Section Detection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SectionDetection

noncomputable section

/-! Global sections detect maps whose source has global section frames
covering the scheme. All nonnegative projective twists have such frames. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory

namespace Construction

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory

def HasFrameSections {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s

def HasFrameSections.lineBundle {X : Scheme.{u}} {M : X.Modules} (h : HasFrameSections M) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := M
  locallyTrivial x := by
    obtain ⟨s, hs⟩ := h x
    exact ⟨AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s, hs, ⟨(AbelianModuli.HilbertConstruction.Section.Frames.sectionFrameIso s).symm⟩⟩

theorem HasFrameSections.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (h : HasFrameSections M) (e : M ≅ N) : HasFrameSections N := by
  intro x
  obtain ⟨s, hs⟩ := h x
  exact ⟨s ≫ e.hom, (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso s e).symm ▸ hs⟩

theorem hasFrameSections_structure (X : Scheme.{u}) : HasFrameSections (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  intro x
  exact ⟨𝟙 _, (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))).symm ▸ trivial⟩

theorem HasFrameSections.tensor {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFrameSections M) (hN : HasFrameSections N) : HasFrameSections (M ⊗ N) := by
  intro x
  obtain ⟨s, hs⟩ := hM x
  obtain ⟨t, ht⟩ := hN x
  let q := Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t
  let e := (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.tensorIso M N).symm
  have he : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing q = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t :=
    Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing (L := hM.lineBundle) (M := hN.lineBundle) s t
  exact ⟨q ≫ e.hom, (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso q e).symm ▸ he.symm ▸ ⟨hs, ht⟩⟩

theorem HasFrameSections.hom_eq_zero {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFrameSections M) (a : M ⟶ N) (ha : a.app ⊤ = 0) : a = 0 := by
  apply Quotients.FiniteDescent.ReducedSectionsEq.Construction.ReducedSections.moduleMap_eq_of_locally
  intro x
  obtain ⟨s, hs⟩ := hM x
  have hsa : s ≫ a = 0 := by
    apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv N).injective
    change a.app ⊤ (s.app ⊤ (1 : Γ(X, ⊤))) = 0
    rw [ha]
    rfl
  let U := AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
  refine ⟨U, hs, ?_⟩
  rw [Functor.map_zero]
  apply (cancel_epi (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s)).mp
  simp only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Category.assoc, ← Functor.map_comp, hsa,
    Functor.map_zero, comp_zero]

theorem HasFrameSections.hom_eq_zero_of_subsingleton {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFrameSections M) [Subsingleton Γ(N, ⊤)] (a : M ⟶ N) : a = 0 := by
  apply hM.hom_eq_zero a
  ext x
  exact Subsingleton.elim _ _

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplane_hasFrameSections (j : σ) :
    HasFrameSections (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) := by
  intro x
  have hx : x ∈ iSup (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) : σ → (Proj _).Opens) := by
    rw [SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i,
    (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := R) j i).symm ▸ hi⟩

theorem coordinatePositiveTwist_hasFrameSections (j : σ) (n : ℕ) :
    HasFrameSections (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) := by
  induction n with
  | zero => exact (hasFrameSections_structure _).of_iso (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.unitIso _).symm
  | succ n ih => exact ih.tensor (coordinateHyperplane_hasFrameSections j)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SectionDetection
