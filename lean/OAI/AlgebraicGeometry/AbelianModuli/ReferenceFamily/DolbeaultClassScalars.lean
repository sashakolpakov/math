import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.Scalars
import OAI.RepresentationTheory.Theta.Geometric.DolbeaultQuotient

/-! # Dolbeault Class Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultClassScalars

noncomputable section

section

/-! Complex multiplication on the original Dolbeault sheaves and their
closed-form kernel gives an actual endomorphism of the short exact sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def dbarScalarSheafMap (q : ℕ) (c : ℂ) :
    DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M q ⟶ DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M q :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom ((c • LinearMap.id : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E U.unop q →ₗ[ℂ]
      DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E U.unop q).toAddMonoidHom)
    naturality := by
      intro U W h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      exact (DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict (E := E) (leOfHom h.unop) (q := q)).map_smul c a }

theorem dbarScalarSheafMap_d (q : ℕ) (c : ℂ) :
    dbarScalarSheafMap E M q c ≫ DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M q =
      DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M q ≫ dbarScalarSheafMap E M (q + 1) c := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact (DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (E := E) U.unop q).map_smul c a

def dbarClosedScalarMap (c : ℂ) : RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M ⟶ RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M :=
  kernel.lift (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)
    (kernel.ι (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1) ≫ dbarScalarSheafMap E M 1 c) (by
      erw [Category.assoc, dbarScalarSheafMap_d, ← Category.assoc, kernel.condition, zero_comp])

theorem dbarClosedScalarMap_ι (c : ℂ) :
    dbarClosedScalarMap E M c ≫ kernel.ι (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1) =
      kernel.ι (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1) ≫ dbarScalarSheafMap E M 1 c :=
  kernel.lift_ι _ _ _

def dbarSequenceScalarMap (c : ℂ) : RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M ⟶ RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M where
  τ₁ := RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarSheafMap E M c
  τ₂ := dbarScalarSheafMap E M 0 c
  τ₃ := dbarClosedScalarMap E M c
  comm₁₂ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    exact (DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldZeroFormLinear (E := E) U.unop).map_smul c g
  comm₂₃ := by
    apply (cancel_mono (kernel.ι (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1))).mp
    change (dbarScalarSheafMap E M 0 c ≫ RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M) ≫ _ =
      (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M ≫ dbarClosedScalarMap E M c) ≫ _
    erw [Category.assoc, RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap_ι, Category.assoc, dbarClosedScalarMap_ι,
      ← Category.assoc, RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap_ι]
    exact dbarScalarSheafMap_d E M 0 c

end

section

/-! The actual Dolbeault connecting class respects the complex scalar
action induced on native holomorphic sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

theorem closedDbarSectionEquiv_scalar (c : ℂ)
    (z : (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M))) :
    RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M ((dbarClosedScalarMap E M c).hom.app (op ⊤) z) =
      c • RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M z := by
  apply Subtype.ext
  exact congrArg (fun f => f.hom.app (op (⊤ : Opens M)) z) (dbarClosedScalarMap_ι E M c)

variable [FiniteDimensional ℂ E]

local instance dbarScalarCohomologyGroup (F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) := Cech.Add.cechClassAddCommGroup (X := TopCat.of M) F n

theorem holomorphicDbarBoundary_scalar (c : ℂ)
    (z : (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M))) :
    RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 E M c (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarBoundary E M z) =
      RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarBoundary E M ((dbarClosedScalarMap E M c).hom.app (op ⊤) z) := by
  let S := RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M
  let hS := RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M
  let φ := dbarSequenceScalarMap E M c
  change (((CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm z).comp hS.extClass (zero_add 1)).comp
    (Ext.mk₀ φ.τ₁) (add_zero 1) = _
  erw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hS φ,
    ← Ext.comp_assoc_of_second_deg_zero]
  exact congrArg (fun a : CategoryTheory.Sheaf.H S.X₃ 0 => a.comp hS.extClass (zero_add 1))
    (CategoryTheory.Sheaf.H.equiv₀_symm_naturality (f := φ.τ₃) isTerminalTop z)

theorem holomorphicDbarClass_scalar (c : ℂ) (a : RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm E M) :
    RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass E M (c • a) =
      RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 E M c (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass E M a) := by
  have he : (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).symm (c • a) =
      (dbarClosedScalarMap E M c).hom.app (op ⊤) ((RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).symm a) := by
    apply (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).injective
    rw [AddEquiv.apply_symm_apply, closedDbarSectionEquiv_scalar, AddEquiv.apply_symm_apply]
  change RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarBoundary E M ((RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).symm (c • a)) = _
  rw [he]
  exact (holomorphicDbarBoundary_scalar E M c _).symm

end

/-! The original additive Dolbeault comparison is complex linear for
the native scalar action on holomorphic sheaf H1. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
    [T2Space M] [CompactSpace M]

local instance dolbeaultLinearNativeH1Group :
    AddCommGroup (CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of M) (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1

def nativeDolbeaultClassLinearEquiv :
    letI := Holomorphic.Scalars.nativeHolomorphicH1Module E M
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace E M ≃ₗ[ℂ] CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 := by
  letI := Holomorphic.Scalars.nativeHolomorphicH1Module E M
  refine { RepresentationTheory.Theta.Geometric.DolbeaultQuotient.dolbeaultOneClassEquiv E M with map_smul' := ?_ }
  intro c q
  refine Quotient.inductionOn' q (fun a => ?_)
  exact holomorphicDbarClass_scalar E M c a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultClassScalars
