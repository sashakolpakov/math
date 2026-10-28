import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCochainMeaning
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit
import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Final

/-! # Compact Support Homeomorph -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph

noncomputable section

/-!
# Actual compact-support transport under homeomorphisms

A homeomorphism gives an order equivalence on the actual compact subsets and
pullback isomorphisms on the actual relative cochain kernels. Passing to their
colimits gives an isomorphism of compact-support cochain complexes. Its maps
agree with ordinary singular pullback after forgetting support, which also
proves identity and composition laws. Taking actual cohomology provides the
compact-support cohomology transport needed for manifold charts.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

section CompactIndices

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The standard equivalence on compact sets also preserves and reflects inclusion. -/
def compactsHomeomorphOrderIso (e : X ≃ₜ Y) : Compacts X ≃o Compacts Y where
  toEquiv := Compacts.equiv e
  map_rel_iff' := by
    intro K L
    change e '' (K : Set X) ⊆ e '' (L : Set X) ↔ K ≤ L
    exact Set.image_subset_image_iff e.injective

@[simp]
theorem compactsHomeomorphOrderIso_apply (e : X ≃ₜ Y) (K : Compacts X) :
    compactsHomeomorphOrderIso e K = Compacts.equiv e K := rfl

/-- Homeomorphisms give equivalences of the actual compact-support index categories. -/
abbrev compactsHomeomorphEquivalence (e : X ≃ₜ Y) : Compacts X ≌ Compacts Y :=
  (compactsHomeomorphOrderIso e).equivalence

/-- A homeomorphism identifies the complements of corresponding compact supports. -/
theorem compactHomeomorph_complement_iff (e : X ≃ₜ Y) (K : Compacts X) (x : X) :
    x ∈ (K : Set X)ᶜ ↔ e x ∈ (Compacts.equiv e K : Set Y)ᶜ := by
  constructor
  · intro hx hmem
    obtain ⟨z, hz, hzx⟩ := hmem
    exact hx (e.injective hzx ▸ hz)
  · intro hx hxK
    exact hx ⟨x, hxK, rfl⟩

end CompactIndices

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable {X Y Z : TopCat.{0}}

/-- Actual pullback of relative cochain kernels at a compact support. -/
def compactSupportHomeomorphStageIso (e : X ≃ₜ Y) (K : Compacts X) :
    CompactSupportCohomology.compactSupportCochainStage M Y (Compacts.equiv e K) ≅ CompactSupportCohomology.compactSupportCochainStage M X K :=
  ImmersionLocalPurity.relativePairHomeomorphCochainIso M e (K : Set X)ᶜ
    (Compacts.equiv e K : Set Y)ᶜ (compactHomeomorph_complement_iff e K)

@[reassoc (attr := simp)]
theorem compactSupportHomeomorphStageIso_inclusion (e : X ≃ₜ Y) (K : Compacts X) :
    (compactSupportHomeomorphStageIso M e K).hom ≫
        CompactSupportCohomology.compactSupportCochainStageInclusion M X K =
      CompactSupportCohomology.compactSupportCochainStageInclusion M Y (Compacts.equiv e K) ≫
        Cohomology.Singular.Functor.singularPullback M (TopCat.isoOfHomeo e).hom :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M (TopCat.isoOfHomeo e).hom
    (fun x hx => (compactHomeomorph_complement_iff e K x).mp hx)

/-- The actual relative pullbacks commute with support enlargement. -/
@[reassoc]
theorem compactSupportHomeomorphStageIso_naturality (e : X ≃ₜ Y)
    {K L : Compacts X} (h : K ≤ L) :
    CompactSupportCohomology.compactSupportCochainMap M ((compactsHomeomorphOrderIso e).monotone h) ≫
        (compactSupportHomeomorphStageIso M e L).hom =
      (compactSupportHomeomorphStageIso M e K).hom ≫ CompactSupportCohomology.compactSupportCochainMap M h := by
  apply (cancel_mono (CompactSupportCohomology.compactSupportCochainStageInclusion M X L)).1
  simp only [Category.assoc, compactSupportHomeomorphStageIso_inclusion,
    CompactSupportCohomology.compactSupportCochainMap_inclusion]
  exact CompactSupportCohomology.compactSupportCochainMap_inclusion_assoc M
    ((compactsHomeomorphOrderIso e).monotone h) _

/-- The homeomorphism acts on the actual compact-support cochain diagrams. -/
def compactSupportHomeomorphDiagramIso (e : X ≃ₜ Y) :
    (compactsHomeomorphEquivalence e).functor ⋙ CompactSupportCohomology.compactSupportCochainDiagram M Y ≅
      CompactSupportCohomology.compactSupportCochainDiagram M X :=
  NatIso.ofComponents (fun K => compactSupportHomeomorphStageIso M e K)
    (fun {_K _L} f => compactSupportHomeomorphStageIso_naturality M e (leOfHom f))

/-- Homeomorphism pullback is an isomorphism of actual compact-support complexes. -/
def compactSupportedCochainsHomeomorphIso (e : X ≃ₜ Y) :
    CompactSupportCohomology.compactSupportedCochains M Y ≅ CompactSupportCohomology.compactSupportedCochains M X :=
  (Functor.Final.colimitIso (compactsHomeomorphEquivalence e).functor
    (CompactSupportCohomology.compactSupportCochainDiagram M Y)).symm ≪≫
      (colim : (Compacts X ⥤ CochainComplex (ModuleCat.{0} R) ℕ) ⥤ _).mapIso
        (compactSupportHomeomorphDiagramIso M e)

/-- The transport is the genuine relative pullback on each compact stage. -/
@[reassoc (attr := simp)]
theorem compactSupportedCochainsHomeomorphIso_ι (e : X ≃ₜ Y) (K : Compacts X) :
    CompactSupportCohomology.compactSupportCochainι M Y (Compacts.equiv e K) ≫
        (compactSupportedCochainsHomeomorphIso M e).hom =
      (compactSupportHomeomorphStageIso M e K).hom ≫ CompactSupportCohomology.compactSupportCochainι M X K := by
  change colimit.ι (CompactSupportCohomology.compactSupportCochainDiagram M Y) (Compacts.equiv e K) ≫
      ((Functor.Final.colimitIso (compactsHomeomorphEquivalence e).functor
        (CompactSupportCohomology.compactSupportCochainDiagram M Y)).inv ≫
          colimMap (compactSupportHomeomorphDiagramIso M e).hom) = _
  exact (Functor.Final.ι_colimitIso_inv_assoc
    (compactsHomeomorphEquivalence e).functor (CompactSupportCohomology.compactSupportCochainDiagram M Y) K
      (colimMap (compactSupportHomeomorphDiagramIso M e).hom)).trans
        (ι_colimMap (compactSupportHomeomorphDiagramIso M e).hom K)

/-- Forgetting support identifies this transport with ordinary singular pullback. -/
@[reassoc (attr := simp)]
theorem compactSupportedCochainsHomeomorphIso_forget (e : X ≃ₜ Y) :
    (compactSupportedCochainsHomeomorphIso M e).hom ≫ CompactSupportCohomology.compactSupportedCochainForget M X =
      CompactSupportCohomology.compactSupportedCochainForget M Y ≫ Cohomology.Singular.Functor.singularPullback M (TopCat.isoOfHomeo e).hom := by
  apply colimit.hom_ext
  intro L
  obtain ⟨K, rfl⟩ := (Compacts.equiv e).surjective L
  rw [compactSupportedCochainsHomeomorphIso_ι_assoc, CompactSupportCohomology.compactSupportCochainι_forget,
    CompactSupportCohomology.compactSupportCochainι_forget_assoc, compactSupportHomeomorphStageIso_inclusion]

@[simp]
theorem compactSupportedCochainsHomeomorphIso_refl (X : TopCat.{0}) :
    compactSupportedCochainsHomeomorphIso M (Homeomorph.refl X) =
      Iso.refl (CompactSupportCohomology.compactSupportedCochains M X) := by
  apply Iso.ext
  apply (cancel_mono (CompactSupportCohomology.compactSupportedCochainForget M X)).1
  rw [compactSupportedCochainsHomeomorphIso_forget, Iso.refl_hom, Category.id_comp]
  change CompactSupportCohomology.compactSupportedCochainForget M X ≫ Cohomology.Singular.Functor.singularPullback M (𝟙 X) = _
  rw [Cohomology.Singular.Functor.singularPullback_id, Category.comp_id]

/-- Homeomorphism pullback composes in the contravariant order. -/
theorem compactSupportedCochainsHomeomorphIso_trans (e : X ≃ₜ Y) (f : Y ≃ₜ Z) :
    compactSupportedCochainsHomeomorphIso M (e.trans f) =
      compactSupportedCochainsHomeomorphIso M f ≪≫ compactSupportedCochainsHomeomorphIso M e := by
  apply Iso.ext
  apply (cancel_mono (CompactSupportCohomology.compactSupportedCochainForget M X)).1
  rw [compactSupportedCochainsHomeomorphIso_forget, Iso.trans_hom, Category.assoc,
    compactSupportedCochainsHomeomorphIso_forget, ← Category.assoc,
    compactSupportedCochainsHomeomorphIso_forget, Category.assoc]
  change CompactSupportCohomology.compactSupportedCochainForget M Z ≫
      Cohomology.Singular.Functor.singularPullback M ((TopCat.isoOfHomeo e).hom ≫ (TopCat.isoOfHomeo f).hom) = _
  rw [Cohomology.Singular.Functor.singularPullback_comp]

@[simp]
theorem compactSupportedCochainsHomeomorphIso_symm (e : X ≃ₜ Y) :
    compactSupportedCochainsHomeomorphIso M e.symm =
      (compactSupportedCochainsHomeomorphIso M e).symm := by
  apply Iso.ext
  apply (cancel_mono (compactSupportedCochainsHomeomorphIso M e).hom).1
  rw [← Iso.trans_hom, ← compactSupportedCochainsHomeomorphIso_trans]
  have he : e.trans e.symm = Homeomorph.refl X := by
    ext x
    exact e.symm_apply_apply x
  rw [he, compactSupportedCochainsHomeomorphIso_refl]
  simp

/-- Cohomology transport at one actual compact support. -/
def compactSupportHomeomorphStageCohomologyIso (e : X ≃ₜ Y) (K : Compacts X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y (Compacts.equiv e K : Set Y)ᶜ n ≅
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n :=
  HomologicalComplex.homologyMapIso (compactSupportHomeomorphStageIso M e K) n

/-- The actual induced homeomorphism isomorphism on compact-support cohomology. -/
def compactSupportedCohomologyHomeomorphIso (e : X ≃ₜ Y) (n : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology M Y n ≅ CompactSupportCohomology.compactSupportedCohomology M X n :=
  HomologicalComplex.homologyMapIso (compactSupportedCochainsHomeomorphIso M e) n

/-- The cohomology transport is induced by genuine relative pullback at every compact stage. -/
@[reassoc (attr := simp)]
theorem compactSupportedCohomologyHomeomorphIso_ι (e : X ≃ₜ Y) (K : Compacts X) (n : ℕ) :
    CompactSupportCohomology.compactSupportCohomologyι M Y (Compacts.equiv e K) n ≫
        (compactSupportedCohomologyHomeomorphIso M e n).hom =
      (compactSupportHomeomorphStageCohomologyIso M e K n).hom ≫
        CompactSupportCohomology.compactSupportCohomologyι M X K n := by
  change HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportCochainι M Y (Compacts.equiv e K)) n ≫
    HomologicalComplex.homologyMap (compactSupportedCochainsHomeomorphIso M e).hom n =
      HomologicalComplex.homologyMap (compactSupportHomeomorphStageIso M e K).hom n ≫
        HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportCochainι M X K) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    compactSupportedCochainsHomeomorphIso_ι]

/-- After support is forgotten, this is ordinary singular cohomology pullback. -/
@[reassoc (attr := simp)]
theorem compactSupportedCohomologyHomeomorphIso_forget (e : X ≃ₜ Y) (n : ℕ) :
    (compactSupportedCohomologyHomeomorphIso M e n).hom ≫
        CompactSupportCohomology.compactSupportedCohomologyForget M X n =
      CompactSupportCohomology.compactSupportedCohomologyForget M Y n ≫
        Cohomology.Singular.Functor.singularCohomologyPullback M (TopCat.isoOfHomeo e).hom n := by
  change HomologicalComplex.homologyMap (compactSupportedCochainsHomeomorphIso M e).hom n ≫
    HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportedCochainForget M X) n =
      HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportedCochainForget M Y) n ≫
        HomologicalComplex.homologyMap (Cohomology.Singular.Functor.singularPullback M (TopCat.isoOfHomeo e).hom) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    compactSupportedCochainsHomeomorphIso_forget]

@[simp]
theorem compactSupportedCohomologyHomeomorphIso_refl (X : TopCat.{0}) (n : ℕ) :
    compactSupportedCohomologyHomeomorphIso M (Homeomorph.refl X) n =
      Iso.refl (CompactSupportCohomology.compactSupportedCohomology M X n) := by
  apply Iso.ext
  change HomologicalComplex.homologyMap
    (compactSupportedCochainsHomeomorphIso M (Homeomorph.refl X)).hom n = 𝟙 _
  rw [compactSupportedCochainsHomeomorphIso_refl, Iso.refl_hom,
    HomologicalComplex.homologyMap_id]

theorem compactSupportedCohomologyHomeomorphIso_trans (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (n : ℕ) :
    compactSupportedCohomologyHomeomorphIso M (e.trans f) n =
      compactSupportedCohomologyHomeomorphIso M f n ≪≫
        compactSupportedCohomologyHomeomorphIso M e n := by
  apply Iso.ext
  change HomologicalComplex.homologyMap (compactSupportedCochainsHomeomorphIso M (e.trans f)).hom n =
    HomologicalComplex.homologyMap (compactSupportedCochainsHomeomorphIso M f).hom n ≫
      HomologicalComplex.homologyMap (compactSupportedCochainsHomeomorphIso M e).hom n
  rw [compactSupportedCochainsHomeomorphIso_trans, Iso.trans_hom,
    HomologicalComplex.homologyMap_comp]

@[simp]
theorem compactSupportedCohomologyHomeomorphIso_symm (e : X ≃ₜ Y) (n : ℕ) :
    compactSupportedCohomologyHomeomorphIso M e.symm n =
      (compactSupportedCohomologyHomeomorphIso M e n).symm := by
  apply Iso.ext
  change HomologicalComplex.homologyMap (compactSupportedCochainsHomeomorphIso M e.symm).hom n =
    HomologicalComplex.homologyMap (compactSupportedCochainsHomeomorphIso M e).inv n
  rw [compactSupportedCochainsHomeomorphIso_symm]
  rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph
