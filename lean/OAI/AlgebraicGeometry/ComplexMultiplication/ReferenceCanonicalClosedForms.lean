import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalGlobalNormalization
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback

/-! # Reference Canonical Closed Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceCanonicalClosedForms

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

section

/-! # Scalar forgetting and integer indexing retain actual closed representatives -/

open _root_.CategoryTheory

local notation "F" => forget₂ (ModuleCat ℂ) AddCommGrpCat
local notation "FN" => Functor.mapHomologicalComplex
  (forget₂ (ModuleCat ℂ) AddCommGrpCat) (ComplexShape.up ℕ)

/-- The integer-indexed additive cycles and the actual native module cycles. -/
def moduleIntegerAdditiveCyclesIso (K : CochainComplex (ModuleCat ℂ) ℕ) (n : ℕ) :
    (((FN).obj K).extend ComplexShape.embeddingUpNat).cycles (n : ℤ) ≅
      (F).obj (K.cycles n) :=
  ((FN).obj K).extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    (K.sc n).mapCyclesIso (F)

set_option backward.isDefEq.respectTransparency false in
/-- This cycle identification retains the actual form or cochain in the retained degree. -/
theorem moduleIntegerAdditiveCyclesIso_hom_i (K : CochainComplex (ModuleCat ℂ) ℕ) (n : ℕ) :
    (moduleIntegerAdditiveCyclesIso K n).hom ≫ (F).map (K.iCycles n) =
      (((FN).obj K).extend ComplexShape.embeddingUpNat).iCycles (n : ℤ) ≫
        (((FN).obj K).extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).hom := by
  dsimp only [moduleIntegerAdditiveCyclesIso, Iso.trans_hom]
  have hi : ((K.sc n).mapCyclesIso (F)).hom ≫ (F).map (K.iCycles n) =
      ((FN).obj K).iCycles n := ShortComplex.mapCyclesIso_hom_iCycles (K.sc n) (F)
  rw [Category.assoc, hi]
  exact HomologicalComplex.extendCyclesIso_hom_iCycles ((FN).obj K)
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl

set_option backward.isDefEq.respectTransparency false in
/-- Scalar forgetting commutes with the class of an actual closed module representative. -/
theorem forgottenModuleHomologyπ (K : CochainComplex (ModuleCat ℂ) ℕ) (n : ℕ) :
    ((FN).obj K).homologyπ n ≫ ((K.sc n).mapHomologyIso (F)).hom =
      ((K.sc n).mapCyclesIso (F)).hom ≫ (F).map (K.homologyπ n) := by
  change ((K.sc n).map (F)).homologyπ ≫ ((K.sc n).mapHomologyIso (F)).hom =
    ((K.sc n).mapCyclesIso (F)).hom ≫ (F).map ((K.sc n).homologyπ)
  let h := (K.sc n).homologyData.left
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq h (F),
    ShortComplex.LeftHomologyData.mapCyclesIso_eq h (F)]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rw [Category.assoc]
  change (h.map (F)).cyclesIso.hom ≫ (F).map h.π ≫ (F).map h.homologyIso.inv = _
  rw [← Functor.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Taking the actual closed class commutes with the full integer additive transport. -/
theorem moduleIntegerAdditiveHomologyIso_π (K : CochainComplex (ModuleCat ℂ) ℕ) (n : ℕ) :
    (((FN).obj K).extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ) ≫
        (Reference.CanonicalGlobalNormalization.moduleIntegerAdditiveHomologyIso K n).hom =
      (moduleIntegerAdditiveCyclesIso K n).hom ≫ (F).map (K.homologyπ n) := by
  dsimp only [Reference.CanonicalGlobalNormalization.moduleIntegerAdditiveHomologyIso, moduleIntegerAdditiveCyclesIso, Iso.trans_hom]
  rw [← Category.assoc, HomologicalComplex.homologyπ_extendHomologyIso_hom,
    Category.assoc, forgottenModuleHomologyπ]
  exact (Category.assoc _ _ _).symm

end

/-! # Original closed global sections retain their literal native smooth-form classes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "K" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor (Y)
local notation "FN" => Functor.mapHomologicalComplex
  (forget₂ (ModuleCat ℂ) AddCommGrpCat) (ComplexShape.up ℕ)
local notation "DR" => OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "G" => OAI.AlgebraicGeometry.Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (Y) Ω•(X)

/-- The literal full smooth form of the original closed holomorphic section. -/
def originalClosedHolomorphicSmoothForm (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p :=
  ⟨ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm X p θ,
    ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm_closed X p θ hθ⟩

set_option backward.isDefEq.respectTransparency false in
/-- The retained component of the original global form map is its actual natural-degree map. -/
theorem originalHolomorphicGlobalToManifoldInt_retained_component (p : ℕ) :
    (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X).f (p : ℤ) ≫
        (((FN).obj (DR)).extendXIso ComplexShape.embeddingUpNat
          (i := p) (i' := (p : ℤ)) rfl).hom =
      (Γ).map ((K).extendXIso ComplexShape.embeddingUpNat
        (i := p) (i' := (p : ℤ)) rfl).hom ≫
          (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldNat X).f p := by
  have hm := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_hom_f (Γ) (K)
    ComplexShape.embeddingUpNat (i := p) (j := (p : ℤ)) rfl
  have hf := HomologicalComplex.extendMap_f (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldNat X)
    ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl
  rw [Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt_normalization, HomologicalComplex.comp_f, hm, hf]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The original extended global section maps to precisely its actual full smooth form. -/
theorem originalHolomorphicGlobalToManifoldInt_retained_section (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤)) :
    (((FN).obj (DR)).extendXIso ComplexShape.embeddingUpNat
        (i := p) (i' := (p : ℤ)) rfl).hom
      ((Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X).f (p : ℤ)
        (CMGlobalSheafCycles.sheafExtendedGlobalSection (Y) (K) p θ)) =
      ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm X p θ := by
  have h := ConcreteCategory.congr_hom
    (originalHolomorphicGlobalToManifoldInt_retained_component X p)
      (CMGlobalSheafCycles.sheafExtendedGlobalSection (Y) (K) p θ)
  simp only [AddCommGrpCat.comp_apply] at h
  have he : (Γ).map ((K).extendXIso ComplexShape.embeddingUpNat
      (i := p) (i' := (p : ℤ)) rfl).hom
      (CMGlobalSheafCycles.sheafExtendedGlobalSection (Y) (K) p θ) = θ := by
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun f => (Γ).map f)
        ((K).extendXIso ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv_hom_id) θ
    simpa only [Functor.map_comp, Functor.map_id, AddCommGrpCat.comp_apply,
      AddCommGrpCat.id_apply, CMGlobalSheafCycles.sheafExtendedGlobalSection] using! hi
  exact h.trans ((congrArg ((Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldNat X).f p) he).trans
    (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldNat_f_apply X p θ))

set_option backward.isDefEq.respectTransparency false in
/-- The original integer-indexed cycle maps to the native cycle of the same literal smooth form. -/
theorem originalClosedHolomorphicGlobalCycle_native_form (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M p).hom
      ((moduleIntegerAdditiveCyclesIso (DR) p).hom
        (HomologicalComplex.cyclesMap (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (p : ℤ)
          (Reference.ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ))) =
      originalClosedHolomorphicSmoothForm X p θ hθ := by
  apply Subtype.ext
  rw [Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamClosedFormsIso_hom_coe]
  have hi := ConcreteCategory.congr_hom (moduleIntegerAdditiveCyclesIso_hom_i (DR) p)
    (HomologicalComplex.cyclesMap (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (p : ℤ)
      (Reference.ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ))
  simp only [AddCommGrpCat.comp_apply] at hi
  have hc := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (p : ℤ))
      (Reference.ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ)
  simp only [AddCommGrpCat.comp_apply, Reference.ClosedGlobalRepresentatives.originalClosedHolomorphicGlobalCycle_iCycles] at hc
  exact hi.trans ((congrArg
    (((FN).obj (DR)).extendXIso ComplexShape.embeddingUpNat
      (i := p) (i' := (p : ℤ)) rfl).hom hc).trans
        (originalHolomorphicGlobalToManifoldInt_retained_section X p θ))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical cohomology transport retains the actual closed smooth-form representative. -/
theorem originalClosedHolomorphicGlobalClass_native_form (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    (Reference.CanonicalGlobalNormalization.originalManifoldIntegerDeRhamCohomologyIso X p).hom
      (HomologicalComplex.homologyMap (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (p : ℤ)
        (Reference.ClosedHolomorphicClasses.originalClosedHolomorphicGlobalClass X p θ hθ)) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M p
        (originalClosedHolomorphicSmoothForm X p θ hθ) := by
  let c := HomologicalComplex.cyclesMap (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (p : ℤ)
    (Reference.ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ)
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (p : ℤ))
      (Reference.ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ)
  simp only [AddCommGrpCat.comp_apply] at hp
  change (Reference.CanonicalGlobalNormalization.originalManifoldIntegerDeRhamCohomologyIso X p).hom
    (HomologicalComplex.homologyMap (Reference.GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (p : ℤ)
      ((G).homologyπ (p : ℤ) (Reference.ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ))) = _
  rw [hp]
  have hi := ConcreteCategory.congr_hom (moduleIntegerAdditiveHomologyIso_π (DR) p) c
  simp only [AddCommGrpCat.comp_apply] at hi
  have hn := ConcreteCategory.congr_hom
    (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso_comp_class E M p)
      ((moduleIntegerAdditiveCyclesIso (DR) p).hom c)
  simp only [ModuleCat.comp_apply] at hn
  exact hi.trans (hn.symm.trans (congrArg (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M p)
    (originalClosedHolomorphicGlobalCycle_native_form X p θ hθ)))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceCanonicalClosedForms
