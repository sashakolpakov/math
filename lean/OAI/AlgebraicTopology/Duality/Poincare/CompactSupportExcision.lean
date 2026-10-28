import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit
import OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual
import OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
import OAI.AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective
import Mathlib.Topology.Category.TopCat.Opens

/-! # Compact Support Excision -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision

noncomputable section

/-!
# Rational cochain excision around compact supports

The maps below are the actual pullbacks of relative singular cochains along
inclusions of pairs. Compact supports in an open subspace are mapped to their
actual compact images in the ambient space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Additive rational duality carries every actual integral-chain
quasi-isomorphism to a cochain quasi-isomorphism. -/
theorem rationalChainDualMap_quasiIso
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) [QuasiIso f] :
    QuasiIso
      (((preadditiveYoneda.obj
          ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj (ModuleCat.of ℚ ℚ))).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)).map f.op)) := by
  let : Injective ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj (ModuleCat.of ℚ ℚ)) :=
    Cohomology.Singular.IntegralCoefficientInjective.injective_restrictScalars_rat
  infer_instance

/-- The native relative rational cochain pullback is a quasi-isomorphism
whenever the native integral relative chain map is a quasi-isomorphism. -/
theorem relativeRationalCochainsMap_quasiIso_of_integral
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) [QuasiIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h)] :
    QuasiIso (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) := by
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let g := RelativeCochainDual.rationalCochainsForget.map
    (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h)
  have : QuasiIso (RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h)) :=
    rationalChainDualMap_quasiIso _
  have : QuasiIso (g ≫ (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom) := by
    change QuasiIso (RelativeCochainDual.rationalCochainsForget.map
      (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) ≫
        (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom)
    rw [RelativeCochainDual.relativeCochainIntegralDualIso_naturality]
    infer_instance
  have : QuasiIso g := quasiIso_of_comp_right g (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) F).mp this

/-- Pullback along the actual pair inclusion `(U,U \ K) → (X,X \ K)`. -/
def compactSupportExcisionCochainMap (X : TopCat.{0}) (U K : Set X) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- The fixed-support comparison restricts the underlying ordinary cochain. -/
@[reassoc (attr := simp)]
theorem compactSupportExcisionCochainMap_inclusion (X : TopCat.{0}) (U K : Set X) :
    compactSupportExcisionCochainMap X U K ≫
        Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ ≫
        Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- Genuine integral excision and injectivity of rational coefficients prove
excision for the actual relative rational cochain restriction. -/
theorem compactSupportExcisionCochainMap_quasiIso (X : TopCat.{0}) (U K : Set X)
    [T2Space X] (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    QuasiIso (compactSupportExcisionCochainMap X U K) := by
  have : QuasiIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)
      (show Set.MapsTo (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) Kᶜ from fun _ h => h)) :=
    AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionChainMap_quasiIso X U K hK hU hKU
  exact relativeRationalCochainsMap_quasiIso_of_integral
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- Fixed-support rational cohomology excision, induced by actual restriction. -/
def compactSupportExcisionCohomologyIso (X : TopCat.{0}) (U K : Set X)
    [T2Space X] (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ n ≅
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) n := by
  have := compactSupportExcisionCochainMap_quasiIso X U K hK hU hKU
  exact isoOfQuasiIsoAt (compactSupportExcisionCochainMap X U K) n

@[simp]
theorem compactSupportExcisionCohomologyIso_hom (X : TopCat.{0}) (U K : Set X)
    [T2Space X] (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    (compactSupportExcisionCohomologyIso X U K hK hU hKU n).hom =
      HomologicalComplex.homologyMap (compactSupportExcisionCochainMap X U K) n := rfl

variable {X : TopCat.{0}}

/-- A compact support in an open subspace, viewed as its actual compact
image in the ambient space. -/
def openSupportImage (U : Opens X) (K : Compacts U) : Compacts X :=
  K.map U.inclusion' U.inclusion'.hom.continuous

@[simp]
theorem openSupportImage_coe (U : Opens X) (K : Compacts U) :
    (openSupportImage U K : Set X) = (Subtype.val : U → X) '' (K : Set U) := rfl

theorem openSupportImage_mono (U : Opens X) {K L : Compacts U} (h : K ≤ L) :
    openSupportImage U K ≤ openSupportImage U L :=
  Set.image_mono h

theorem openSupportImage_subset (U : Opens X) (K : Compacts U) :
    (openSupportImage U K : Set X) ⊆ U := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

@[simp]
theorem openSupportImage_preimage (U : Opens X) (K : Compacts U) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X)) ⁻¹' (openSupportImage U K : Set X) =
      (K : Set U) := by
  change (Subtype.val : U → X) ⁻¹' (Subtype.val '' (K : Set U)) = (K : Set U)
  exact Set.preimage_image_eq _ Subtype.val_injective

@[simp]
theorem openSupportImage_preimage_compl (U : Opens X) (K : Compacts U) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X)) ⁻¹' (openSupportImage U K : Set X)ᶜ =
      (K : Set U)ᶜ := by
  rw [Set.preimage_compl, openSupportImage_preimage]

/-- The actual relative cochain restriction for a compact support in an
open subspace, with that subspace's original support as its target. -/
def compactSupportOpenStageRestriction (U : Opens X) (K : Compacts U) :
    CompactSupportCohomology.compactSupportCochainStage (ModuleCat.of ℚ ℚ) X (openSupportImage U K) ⟶
      CompactSupportCohomology.compactSupportCochainStage (ModuleCat.of ℚ ℚ) (TopCat.of U) K :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) U.inclusion' (by
    rintro x hx ⟨y, hy, hxy⟩
    exact hx ((Subtype.ext hxy) ▸ hy))

@[reassoc (attr := simp)]
theorem compactSupportOpenStageRestriction_inclusion (U : Opens X) (K : Compacts U) :
    compactSupportOpenStageRestriction U K ≫
        CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U) K =
      CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) X (openSupportImage U K) ≫
        Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) U.inclusion' :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) U.inclusion' _

/-- The actual pair restrictions commute with enlarging compact supports. -/
@[reassoc]
theorem compactSupportOpenStageRestriction_naturality (U : Opens X)
    {K L : Compacts U} (h : K ≤ L) :
    CompactSupportCohomology.compactSupportCochainMap (ModuleCat.of ℚ ℚ) (openSupportImage_mono U h) ≫
        compactSupportOpenStageRestriction U L =
      compactSupportOpenStageRestriction U K ≫
        CompactSupportCohomology.compactSupportCochainMap (ModuleCat.of ℚ ℚ) h := by
  apply (cancel_mono
    (CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U) L)).1
  simp only [Category.assoc, compactSupportOpenStageRestriction_inclusion,
    CompactSupportCohomology.compactSupportCochainMap_inclusion, CompactSupportCohomology.compactSupportCochainMap_inclusion_assoc]

private theorem relativeCochainInclusion_eqToHom (Y : TopCat.{0})
    {A B : Set Y} (h : A = B) :
    eqToHom (congrArg (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y) h) ≫
        Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y B =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y A := by
  subst B
  simp

private def compactSupportOpenPreimageIso (U : Opens X) (K : Compacts U) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X)) ⁻¹' (openSupportImage U K : Set X)ᶜ) ≅
        CompactSupportCohomology.compactSupportCochainStage (ModuleCat.of ℚ ℚ) (TopCat.of U) K :=
  eqToIso (congrArg (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U))
    (openSupportImage_preimage_compl U K))

private theorem compactSupportOpenPreimageIso_inclusion (U : Opens X) (K : Compacts U) :
    (compactSupportOpenPreimageIso U K).hom ≫
        CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U) K =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X)) ⁻¹' (openSupportImage U K : Set X)ᶜ) :=
  relativeCochainInclusion_eqToHom _ (openSupportImage_preimage_compl U K)

private theorem compactSupportOpenStageRestriction_eq (U : Opens X) (K : Compacts U) :
    compactSupportExcisionCochainMap X (U : Set X) (openSupportImage U K : Set X) ≫
        (compactSupportOpenPreimageIso U K).hom =
      compactSupportOpenStageRestriction U K := by
  apply (cancel_mono
    (CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U) K)).1
  rw [Category.assoc, compactSupportOpenPreimageIso_inclusion]
  exact (compactSupportExcisionCochainMap_inclusion X (U : Set X)
    (openSupportImage U K : Set X)).trans
      (compactSupportOpenStageRestriction_inclusion U K).symm

/-- The support-stage restriction, with its original local compact set, is
a quasi-isomorphism. Only openness, compactness, and Hausdorffness are used. -/
theorem compactSupportOpenStageRestriction_quasiIso [T2Space X]
    (U : Opens X) (K : Compacts U) :
    QuasiIso (compactSupportOpenStageRestriction U K) := by
  have := compactSupportExcisionCochainMap_quasiIso X (U : Set X)
    (openSupportImage U K : Set X) (openSupportImage U K).isCompact U.isOpen
    (openSupportImage_subset U K)
  rw [← compactSupportOpenStageRestriction_eq]
  infer_instance

/-- The canonical excision isomorphism for a compact support in an open
subspace, expressed using that compact set on both sides. -/
def compactSupportOpenStageIso [T2Space X] (U : Opens X) (K : Compacts U) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (openSupportImage U K : Set X)ᶜ n ≅
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (K : Set U)ᶜ n := by
  have := compactSupportOpenStageRestriction_quasiIso U K
  exact isoOfQuasiIsoAt (compactSupportOpenStageRestriction U K) n

@[simp]
theorem compactSupportOpenStageIso_hom [T2Space X] (U : Opens X) (K : Compacts U) (n : ℕ) :
    (compactSupportOpenStageIso U K n).hom =
      HomologicalComplex.homologyMap (compactSupportOpenStageRestriction U K) n := rfl

/-- Excision commutes with enlargement of compact supports. -/
@[reassoc]
theorem compactSupportOpenStageIso_naturality [T2Space X] (U : Opens X)
    {K L : Compacts U} (h : K ≤ L) (n : ℕ) :
    CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) (openSupportImage_mono U h) n ≫
        (compactSupportOpenStageIso U L n).hom =
      (compactSupportOpenStageIso U K n).hom ≫
        CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h n := by
  simp only [compactSupportOpenStageIso_hom, CompactSupportColimit.compactSupportCohomologyMap,
    ← HomologicalComplex.homologyMap_comp]
  rw [compactSupportOpenStageRestriction_naturality]

/-- Inverse excision is compatible with the same support transitions. -/
@[reassoc]
theorem compactSupportOpenStageIso_inv_naturality [T2Space X] (U : Opens X)
    {K L : Compacts U} (h : K ≤ L) (n : ℕ) :
    CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h n ≫
        (compactSupportOpenStageIso U L n).inv =
      (compactSupportOpenStageIso U K n).inv ≫
        CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) (openSupportImage_mono U h) n := by
  apply (cancel_mono (compactSupportOpenStageIso U L n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [compactSupportOpenStageIso_naturality, Iso.inv_hom_id_assoc]

/-- Extension from an open subspace on actual compactly supported rational
cohomology. Its definition uses inverse excision on each compact support and
the proved colimit universal property of compactly supported cohomology. -/
def compactSupportOpenExtension [T2Space X] (U : Opens X) (n : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n ⟶
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n :=
  CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) (TopCat.of U) n
    (fun K => (compactSupportOpenStageIso U K n).inv ≫
      CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X (openSupportImage U K) n)
    (by
      intro K L h
      rw [← Category.assoc, compactSupportOpenStageIso_inv_naturality,
        Category.assoc, CompactSupportColimit.compactSupportCohomologyMap_ι])

/-- On every compact stage, open extension is precisely inverse excision
followed by the ambient compact-support insertion. -/
@[reassoc (attr := simp)]
theorem compactSupportCohomologyι_openExtension [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ) :
    CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K n ≫
        compactSupportOpenExtension U n =
      (compactSupportOpenStageIso U K n).inv ≫
        CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X (openSupportImage U K) n :=
  CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) (TopCat.of U) n _ _ K

/-- The compact-stage inverse-excision formula uniquely specifies extension
from the open subspace. -/
theorem compactSupportOpenExtension_unique [T2Space X] (U : Opens X) (n : ℕ)
    (f : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n ⟶
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n)
    (hf : ∀ K : Compacts U,
      CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K n ≫ f =
        (compactSupportOpenStageIso U K n).inv ≫
          CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X (openSupportImage U K) n) :
    f = compactSupportOpenExtension U n := by
  apply CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of U) n
  intro K
  rw [hf, compactSupportCohomologyι_openExtension]

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision
