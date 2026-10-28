import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Local -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Local

noncomputable section

section

/-! # Local representatives of the original form sheaves

Every original sheaf section is locally an original quotient form. Its actual
smooth tangent values therefore retain the genuine pure holomorphic type.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "J" => Opens.grothendieckTopology (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

/-- An original sheaf section has an actual quotient-form representative near every point. -/
theorem originalHolomorphicSheaf_local_representative (p : ℕ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op U)) (x : U) :
    ∃ (V : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (h : V ≤ U) (_hx : x.val ∈ V)
      (a : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op V) p),
      (toSheafify J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)).app (Opposite.op V) a =
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.map (homOfLE h).op θ := by
  have hcover := CategoryTheory.Presheaf.imageSieve_mem J
    (toSheafify J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)) θ
  obtain ⟨V, i, ⟨a, ha⟩, hx⟩ := hcover x.val x.property
  exact ⟨V, i.le, hx, a, ha⟩

/-- The sheaf map has exactly the actual quotient-form values on a local representative. -/
theorem originalHolomorphicToSmoothSheaf_unit_apply (p : ℕ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (a : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) :
    (FormSheaf.originalHolomorphicToSmoothSheaf X p).hom.app (Opposite.op U)
      ((toSheafify J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)).app (Opposite.op U) a) =
        OpenForms.originalHolomorphicToSmoothOpenForm X U p a := by
  exact congrArg (fun f => f.app (Opposite.op U) a)
    (FormSheaf.originalHolomorphicToSmoothSheaf_unit X p)

/-- The actual tangent values of every original holomorphic sheaf section have type (p,0). -/
def originalHolomorphicToSmoothSheafSection (p : ℕ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) :
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op U) →+
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm Model U p :=
  ((FormSheaf.originalHolomorphicToSmoothSheaf X p).hom.app (Opposite.op U)).hom

/-- The actual tangent values of every original holomorphic sheaf section have type (p,0). -/
theorem originalHolomorphicToSmoothSheaf_pure (p : ℕ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op U))
    (x : U) (z : ℂˣ)
    (v : Fin p → TangentSpace 𝓘(ℝ, Model) x.val) :
    originalHolomorphicToSmoothSheafSection X p U θ x
        (fun i => Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (E := Model) x.val (↑(z⁻¹) : ℂ) (v i)) =
      (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ 0)⁻¹) *
        originalHolomorphicToSmoothSheafSection X p U θ x v := by
  obtain ⟨V, h, hx, a, ha⟩ := originalHolomorphicSheaf_local_representative X p U θ x
  have hn := NatTrans.naturality_apply (FormSheaf.originalHolomorphicToSmoothSheaf X p).hom
    (homOfLE h).op θ
  have hl : OpenForms.originalHolomorphicToSmoothOpenForm X V p a =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h
        (originalHolomorphicToSmoothSheafSection X p U θ) := by
    rw [← originalHolomorphicToSmoothSheaf_unit_apply X p V a, ha]
    exact hn
  have hpoint := congrArg (fun f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm Model V p =>
    f ⟨x.val, hx⟩) hl
  have hp := CovectorRealForm.complexCovectorFieldToRealForm_hasTangentBidegree p
    (Reference.RealFormSmooth.originalHolomorphicOriginalComplexField X V p a) x.val z v
  change OpenForms.originalHolomorphicToSmoothOpenForm X V p a ⟨x.val, hx⟩
      (fun i => Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (E := Model) x.val (↑(z⁻¹) : ℂ) (v i)) =
    (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ 0)⁻¹) *
      OpenForms.originalHolomorphicToSmoothOpenForm X V p a ⟨x.val, hx⟩ v at hp
  rw [hpoint] at hp
  exact hp

/-- Actual global smooth forms obtained from the original global holomorphic sheaf sections. -/
def originalHolomorphicSheafToGlobalSmoothForm (p : ℕ) :
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤) →+
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm Model (ComplexPoint.Basic.ComplexSchemePoint X) p :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal.toAddMonoidHom.comp
    (originalHolomorphicToSmoothSheafSection X p ⊤)

/-- Every original global holomorphic sheaf section is a genuine pure (p,0) smooth form. -/
theorem originalHolomorphicSheafToGlobalSmoothForm_pure (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤)) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree Model (ComplexPoint.Basic.ComplexSchemePoint X) p 0
      (originalHolomorphicSheafToGlobalSmoothForm X p θ :
        Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm Model (ComplexPoint.Basic.ComplexSchemePoint X) p) := by
  intro x z v
  have heval : (originalHolomorphicSheafToGlobalSmoothForm X p θ :
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm Model (ComplexPoint.Basic.ComplexSchemePoint X) p) x =
        originalHolomorphicToSmoothSheafSection X p ⊤ θ ⟨x, by simp⟩ :=
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply
      (originalHolomorphicToSmoothSheafSection X p ⊤ θ) x
  calc
    _ = originalHolomorphicToSmoothSheafSection X p ⊤ θ ⟨x, by simp⟩
        (fun i => Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (E := Model) x (↑(z⁻¹) : ℂ) (v i)) :=
      congrArg (fun c => c
        (fun i => Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (E := Model) x (↑(z⁻¹) : ℂ) (v i))) heval
    _ = (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ 0)⁻¹) *
        originalHolomorphicToSmoothSheafSection X p ⊤ θ ⟨x, by simp⟩ v :=
      originalHolomorphicToSmoothSheaf_pure X p ⊤ θ ⟨x, by simp⟩ z v
    _ = _ := congrArg (fun c => (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ 0)⁻¹) * c v) heval.symm

/-- The actual global smooth-form map preserves the original global sheaf differential. -/
theorem originalHolomorphicSheafToGlobalSmoothForm_differential (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤)) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (originalHolomorphicSheafToGlobalSmoothForm X p θ) =
      originalHolomorphicSheafToGlobalSmoothForm X (p + 1)
        ((ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ) := by
  have hd := congrArg (fun f => f.hom.app (Opposite.op ⊤) θ)
    (FormSheaf.originalHolomorphicToSmoothSheaf_differential X p)
  exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_d
    (originalHolomorphicToSmoothSheafSection X p ⊤ θ)).trans
      (congrArg Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal hd.symm)

/-- Closed original global sections give actual closed pure holomorphic tangent forms. -/
theorem originalHolomorphicSheafToGlobalSmoothForm_closed (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (originalHolomorphicSheafToGlobalSmoothForm X p θ) = 0 := by
  rw [originalHolomorphicSheafToGlobalSmoothForm_differential, hθ, map_zero]

end

section

/-! # Faithfulness of the actual tangent values of original holomorphic sheaf sections -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "J" => Opens.grothendieckTopology (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

/-- Genuine tangent evaluation is locally injective before sheafification. -/
theorem originalHolomorphicToSmoothPresheaf_locallyInjective (p : ℕ) :
    Presheaf.IsLocallyInjective J (FormSheaf.originalHolomorphicToSmoothPresheaf X p) :=
  Presheaf.isLocallyInjective_of_injective J _
    (fun U => OpenForms.originalHolomorphicToSmoothOpenForm_injective X U.unop p)

/-- Sheafification retains faithfulness of genuine cotangent evaluation. -/
theorem originalHolomorphicToSmoothSheaf_locallyInjective (p : ℕ) :
    CategoryTheory.Sheaf.IsLocallyInjective (FormSheaf.originalHolomorphicToSmoothSheaf X p) := by
  have : Presheaf.IsLocallyInjective J (FormSheaf.originalHolomorphicToSmoothPresheaf X p) :=
    originalHolomorphicToSmoothPresheaf_locallyInjective X p
  have : Presheaf.IsLocallyInjective J
      (toSheafify J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) ≫
        (FormSheaf.originalHolomorphicToSmoothSheaf X p).hom) := by
    rw [FormSheaf.originalHolomorphicToSmoothSheaf_unit]
    infer_instance
  exact (Presheaf.comp_isLocallyInjective_iff J
    (toSheafify J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p))
    (FormSheaf.originalHolomorphicToSmoothSheaf X p).hom).mp inferInstance

/-- Actual smooth values determine every original holomorphic sheaf section uniquely. -/
theorem originalHolomorphicToSmoothSheafSection_injective (p : ℕ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) :
    Function.Injective (originalHolomorphicToSmoothSheafSection X p U) := by
  have := originalHolomorphicToSmoothSheaf_locallyInjective X p
  exact (CategoryTheory.Sheaf.isLocallyInjective_iff_injective
    (FormSheaf.originalHolomorphicToSmoothSheaf X p)).mp inferInstance (Opposite.op U)

/-- The actual original-to-smooth form sheaf map is a monomorphism. -/
instance originalHolomorphicToSmoothSheaf_mono (p : ℕ) :
    Mono (FormSheaf.originalHolomorphicToSmoothSheaf X p) := by
  have := originalHolomorphicToSmoothSheaf_locallyInjective X p
  exact CategoryTheory.Sheaf.mono_of_isLocallyInjective _

end

/-! # Gluing actual original holomorphic representatives from their smooth values -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

/-- Local lifts through a sectionwise injective sheaf map glue to a unique actual section. -/
theorem sheafSection_existsUnique_of_local_images {T : TopCat.{0}}
    (F G : TopCat.Sheaf AddCommGrpCat.{0} T) (φ : F ⟶ G)
    (hφ : ∀ V : Opens T, Function.Injective (φ.hom.app (op V)))
    (U : Opens T) (s : G.presheaf.obj (op U))
    (hloc : ∀ x : U, ∃ (V : Opens T) (h : V ≤ U) (_hx : x.val ∈ V)
      (t : F.presheaf.obj (op V)),
      φ.hom.app (op V) t = G.presheaf.map (homOfLE h).op s) :
    ∃! t : F.presheaf.obj (op U), φ.hom.app (op U) t = s := by
  classical
  choose V hV hx t ht using hloc
  have hcover : U ≤ iSup V := by
    intro x hxu
    exact (le_iSup V ⟨x, hxu⟩) (hx ⟨x, hxu⟩)
  have hc : TopCat.Presheaf.IsCompatible F.presheaf V t := by
    intro x y
    apply hφ (V x ⊓ V y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht x, ht y]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.presheaf.map_comp, ← G.presheaf.map_comp]
    rfl
  obtain ⟨g, hg, _hunique⟩ := F.existsUnique_gluing' V U
    (fun x => homOfLE (hV x)) hcover t hc
  have himage : φ.hom.app (op U) g = s := by
    apply G.eq_of_locally_eq' V U (fun x => homOfLE (hV x)) hcover
    intro x
    rw [← NatTrans.naturality_apply, hg x, ht x]
  exact ⟨g, himage, fun g' hg' => hφ U (hg'.trans himage.symm)⟩

open _root_.AlgebraicGeometry ComplexPoint
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "J" => Opens.grothendieckTopology (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

/-- Actual local quotient forms with the same smooth values give a unique original sheaf section. -/
theorem originalHolomorphicSheaf_existsUnique_of_local_forms (p : ℕ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (s : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm Model U p)
    (hloc : ∀ x : U, ∃ (V : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (h : V ≤ U)
      (_hx : x.val ∈ V) (t : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) (op V) p),
      OpenForms.originalHolomorphicToSmoothOpenForm X V p t =
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h s) :
    ∃! θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (op U),
      originalHolomorphicToSmoothSheafSection X p U θ = s := by
  apply sheafSection_existsUnique_of_local_images
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) (FormSheaf.originalSmoothFormAddSheaf X p)
    (FormSheaf.originalHolomorphicToSmoothSheaf X p)
    (originalHolomorphicToSmoothSheafSection_injective X p) U s
  intro x
  obtain ⟨V, h, hx, t, ht⟩ := hloc x
  refine ⟨V, h, hx,
    (toSheafify J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)).app (op V) t, ?_⟩
  exact (originalHolomorphicToSmoothSheaf_unit_apply X p V t).trans ht

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Local
