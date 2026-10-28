import OAI.RepresentationTheory.Theta.Geometric.NonvanishingFunctorComparison

/-! # Nonvanishing Scalar Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.NonvanishingScalarPullback

noncomputable section

/-! Pullback of a scalar section has exactly the inverse-image basic open. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem endValue_unitEndomorphism {X : Scheme} (r : Γ(X, ⊤)) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) = r := by
  change 1 * X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) r = r
  rw [one_mul]
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (Opposite.op (⊤ : X.Opens))) r

theorem unitEndomorphism_endValue {X : Scheme} (a : End (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) :
    AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X a) = a :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X (endValue_unitEndomorphism _)

theorem sectionNonvanishing_unitEndomorphism {X : Scheme} (r : Γ(X, ⊤)) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) = X.basicOpen r := by
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar, endValue_unitEndomorphism]

theorem sectionNonvanishing_pullback_scalar {X Y : Scheme} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r)) =
      X.basicOpen (f.appTop r) := by
  let a := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm ≪≫ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f
  have h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) ≫
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).hom = a.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (f.appTop r) := by
    change ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r)) ≫ _ = _
    rw [Category.assoc, Pullback.Algebraic.pullback_unitEndomorphism]
    rfl
  have hN := congrArg AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing h
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction.sectionNonvanishing_sourceIso,
    sectionNonvanishing_unitEndomorphism] at hN
  exact hN

theorem sectionNonvanishing_pullback_framed {X Y : Scheme} (f : X ⟶ Y)
    {M : Y.Modules} (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) = f ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
  have h₁ := NonvanishingFunctorComparison.sectionNonvanishing_pullback_targetIso f s e
  have h₂ := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso s e
  rw [← unitEndomorphism_endValue (s ≫ e.hom), sectionNonvanishing_unitEndomorphism] at h₂
  rw [← unitEndomorphism_endValue (s ≫ e.hom), sectionNonvanishing_pullback_scalar] at h₁
  rw [← h₁, ← h₂]
  exact (f.preimage_basicOpen_top _).symm

end

end OAI.RepresentationTheory.Theta.Geometric.NonvanishingScalarPullback
