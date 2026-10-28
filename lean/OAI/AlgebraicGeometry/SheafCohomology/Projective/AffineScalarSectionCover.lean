import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteSectionCombination
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Affine Scalar Section Cover -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineScalarSectionCover

noncomputable section

/-! A finite epimorphic family of scalar sections covers an affine scheme by its frame opens. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

universe u

local instance scalarSectionCoverBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem affine_scalar_sections_span {X : Scheme.{u}} [IsAffine X] {ι : Type} [Fintype ι]
    (s : ι → End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) [Epi (Sigma.desc s)] :
    Ideal.span (Set.range (fun i => AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (s i))) = ⊤ := by
  have hunit : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent :=
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf X)
  have : (∐ fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ (fun _ => hunit)
  let F : X.Modules ⥤ ModuleCat Γ(X, ⊤) := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have : F.Additive := { map_add := by intros; ext; rfl }
  obtain ⟨x, hx⟩ := Quasicoherent.Scheme.Modules.isQuasicoherent_surjective_of_epi (Sigma.desc s)
    (1 : Γ(X, ⊤))
  let c : ι → Γ(X, ⊤) := fun i =>
    F.map (CoproductMatrixComponents.finiteCoproductProjection (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) i) x
  have hsum : ∑ i, c i * AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (s i) = 1 := by
    have h := FiniteSectionCombination.finiteCoproduct_desc_value F (fun _ : ι => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) s x
    have hi (i : ι) : F.map (s i) (c i) = c i * AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (s i) := by
      change ((s i).val.app (op ⊤)) (c i) =
        c i • ((s i).val.app (op ⊤)) (1 : Γ(X, ⊤))
      rw [← ((s i).val.app (op ⊤)).hom.map_smul]
      simp only [smul_eq_mul, mul_one]
    simpa only [← hi] using h.symm.trans hx
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  rw [← hsum]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

theorem affine_scalar_sections_cover {X : Scheme.{u}} [IsAffine X] {ι : Type} [Fintype ι]
    (s : ι → End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) [Epi (Sigma.desc s)] :
    ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  have hU := iSup_basicOpen_of_span_eq_top (⊤ : X.Opens)
    (Set.range (fun i => AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (s i))) (affine_scalar_sections_span s)
  intro x
  have hx : x ∈ ⨆ r ∈ Set.range (fun i => AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (s i)), X.basicOpen r := by
    rw [hU]
    trivial
  obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hx
  obtain ⟨⟨i, rfl⟩, hi⟩ := Opens.mem_iSup.mp hr
  exact ⟨i, (AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar (s i)).symm ▸ hi⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineScalarSectionCover
