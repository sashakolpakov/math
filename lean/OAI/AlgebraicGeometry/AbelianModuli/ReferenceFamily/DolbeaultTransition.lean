import OAI.RepresentationTheory.Theta.Geometric.DolbeaultBoundary
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero
import OAI.AlgebraicGeometry.DivisorClass.Chern.TransitionIntrinsicResolution
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

/-! # Dolbeault Transition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition

noncomputable section

section

/-! Evaluate the actual Dolbeault transition cocycle as differences of
its smooth local scalar primitives, then exponentiate those differences. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] [FiniteDimensional ℂ E]
  (a : RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm E M)
  (l : DivisorClass.Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M)
    ((RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).symm a))

def dbarZeroFormEvaluation (U : Opens M) (x : U) : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E U 0 →ₗ[ℂ] ℂ where
  toFun z := z.val x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dbarLiftZeroForm (i : M) : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (l.domain i) 0 := l.section_ i

def dbarTransitionFunction (b : Fin 2 → M) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b) :=
  l.transitionCech (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M) b

theorem dbarTransitionFunction_value (b : Fin 2 → M) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b) :
    dbarTransitionFunction E M a l b x =
      (dbarLiftZeroForm E M a l (b 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 1 x.property⟩ 0 -
        (dbarLiftZeroForm E M a l (b 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 0 x.property⟩ 0 := by
  have h := congrFun (l.transitionCech_map (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M)) b
  rw [DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta (X := TopCat.of M)] at h
  let v := dbarZeroFormEvaluation E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b) x
  have hv := congrArg v h
  have hl : v (DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) l.domain
      (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M).f.hom 1
        (l.transitionCech (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M)) b) =
      dbarTransitionFunction E M a l b x :=
    DivisorClass.Chern.Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply (dbarTransitionFunction E M a l b) x 0
  have hr := map_sub v
    (DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M).X₂
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 1) (l.section_ (b 1)))
    (DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M).X₂
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 0) (l.section_ (b 0)))
  exact hl.symm.trans (hv.trans hr)

def dbarTransitionUnitCech : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj l.domain 1 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) l.domain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicExponentialSheafMap E M).hom 1
    (l.transitionCech (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M))

theorem dbarTransitionUnitCech_closed :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj l.domain 1 (dbarTransitionUnitCech E M a l) = 0 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient_closed (X := TopCat.of M) l.domain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicExponentialSheafMap E M).hom 1
    (l.transitionCech (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M))
    (l.transitionCech_closed (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M))

theorem dbarTransitionUnitCech_value (b : Fin 2 → M) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b) (dbarTransitionUnitCech E M a l b)).val x =
      Complex.exp ((dbarLiftZeroForm E M a l (b 1)).val
        ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 1 x.property⟩ 0 -
          (dbarLiftZeroForm E M a l (b 0)).val
            ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 0 x.property⟩ 0) :=
  congrArg Complex.exp (dbarTransitionFunction_value E M a l b x)

theorem dbarTransitionUnitCech_class :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) l.domain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M) l.iSup_domain 0
      (dbarTransitionUnitCech E M a l) (dbarTransitionUnitCech_closed E M a l) =
        RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 E M (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass E M a) := by
  have h : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) l.domain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M)
      l.iSup_domain 0 (l.transitionCech (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M))
        (l.transitionCech_closed (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M)) =
      RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass E M a :=
    l.transitionCech_sheaf_class (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M)
  have hn := DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass_naturality (X := TopCat.of M) l.domain
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicExponentialSheafMap E M) l.iSup_domain 0
    (l.transitionCech (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M))
    (l.transitionCech_closed (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M))
  exact hn.symm.trans (congrArg (RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 E M) h)

end

section

/-! Actual transition values identify a holomorphic unit class with the
exponential of a specified Dolbeault class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] [FiniteDimensional ℂ E]
  (a : RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm E M)
  (l : DivisorClass.Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M)
    ((RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).symm a))

theorem holomorphicUnitCech_class_eq_dbar_of_values
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj l.domain 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj l.domain 1 k = 0)
    (hv : ∀ (b : Fin 2 → M) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b),
      (Holomorphic.LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b) (k b)).val x =
        Complex.exp ((dbarLiftZeroForm E M a l (b 1)).val
          ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 1 x.property⟩ 0 -
            (dbarLiftZeroForm E M a l (b 0)).val
              ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain b 0 x.property⟩ 0)) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) l.domain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M) l.iSup_domain 0 k hk =
      RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 E M (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass E M a) := by
  have he : k = dbarTransitionUnitCech E M a l := by
    funext b
    apply Holomorphic.GlobalGluing.holomorphicUnitSection_ext E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain b)
    intro x
    exact (hv b x).trans (dbarTransitionUnitCech_value E M a l b x).symm
  exact (Cech.Add.cechSheafClass_congr (X := TopCat.of M) l.domain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
    l.iSup_domain 0 k (dbarTransitionUnitCech E M a l) hk
    (dbarTransitionUnitCech_closed E M a l) he).trans (dbarTransitionUnitCech_class E M a l)

end

section

/-! Glue the actual images of local smooth primitives whenever their
differences are holomorphic, using the original closed Dolbeault sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

theorem shortComplex_local_images_glue {X : TopCat}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X))
    (U : X → Opens X) (hU : ∀ x, x ∈ U x)
    (b : ∀ i, S.X₂.obj.obj (op (U i)))
    (η : ∀ i j, S.X₁.obj.obj (op (U i ⊓ U j)))
    (hη : ∀ i j, S.f.hom.app (op (U i ⊓ U j)) (η i j) =
      DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (b j) - DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (b i)) :
    ∃ t : S.X₃.obj.obj (op (⊤ : Opens X)),
      ∀ i, S.g.hom.app (op (U i)) (b i) = DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top t := by
  let v (i : X) := S.g.hom.app (op (U i)) (b i)
  have hc : TopCat.Presheaf.IsCompatible S.X₃.obj U v := by
    intro i j
    have hz : S.g.hom.app (op (U i ⊓ U j)) (S.f.hom.app (op (U i ⊓ U j)) (η i j)) = 0 := by
      change (S.f ≫ S.g).hom.app (op (U i ⊓ U j)) (η i j) = 0
      rw [S.zero]
      rfl
    rw [hη, map_sub, DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict, DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict] at hz
    exact (sub_eq_zero.mp hz).symm
  have hcover : (⊤ : Opens X) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hU x⟩
  obtain ⟨t, ht, _⟩ := S.X₃.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover v hc
  exact ⟨t, fun i => (ht i).symm⟩

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

structure DolbeaultPrimitiveSystem where
  domain : M → Opens M
  mem_domain : ∀ x, x ∈ domain x
  primitive : ∀ i, DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (domain i) 0
  difference : ∀ i j, DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := ↥(domain i ⊓ domain j))
  difference_map : ∀ i j,
    (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M).f.hom.app (op (domain i ⊓ domain j)) (difference i j) =
      DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict inf_le_right (primitive j) -
        DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict inf_le_left (primitive i)

namespace DolbeaultPrimitiveSystem

variable (D : DolbeaultPrimitiveSystem E M)

theorem exists_closedSection :
    ∃ t : (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M)),
      ∀ i, (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M).hom.app (op (D.domain i)) (D.primitive i) =
        DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M) le_top t :=
  shortComplex_local_images_glue (X := TopCat.of M) (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M)
    D.domain D.mem_domain D.primitive D.difference D.difference_map

def closedSection : (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M)) :=
  Classical.choose (D.exists_closedSection E M)

theorem closedSection_restrict (i : M) :
    (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M).hom.app (op (D.domain i)) (D.primitive i) =
      DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M) le_top (D.closedSection E M) :=
  Classical.choose_spec (D.exists_closedSection E M) i

def closedForm : RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm E M := RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M (D.closedSection E M)

theorem closedForm_restrict (i : M) :
    DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (D.domain i) 0 (D.primitive i) =
      DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict le_top (D.closedForm E M).val := by
  let ι := kernel.ι (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)
  have h := congrArg (ι.hom.app (op (D.domain i))) (D.closedSection_restrict E M i)
  have hl : ι.hom.app (op (D.domain i))
      ((RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M).hom.app (op (D.domain i)) (D.primitive i)) =
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (D.domain i) 0 (D.primitive i) := by
    change (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M ≫ ι).hom.app (op (D.domain i)) (D.primitive i) = _
    rw [RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap_ι]
    rfl
  exact hl.symm.trans (h.trans (DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict ι (show D.domain i ≤ ⊤ from le_top)
    (D.closedSection E M)))

def liftCover : DivisorClass.Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedMap E M)
    ((RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).symm (D.closedForm E M)) where
  domain := D.domain
  mem_domain := D.mem_domain
  section_ := D.primitive
  image i := (D.closedSection_restrict E M i).trans
    (congrArg (DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M) (show D.domain i ≤ ⊤ from le_top))
      ((RepresentationTheory.Theta.Geometric.DolbeaultBoundary.closedDbarSectionEquiv E M).symm_apply_apply (D.closedSection E M))).symm

theorem liftCover_transition [FiniteDimensional ℂ E] (i j : M) :
    (D.liftCover E M).transition (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M) i j =
      D.difference i j := by
  have : Mono (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M).f :=
    (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M).mono_f
  apply DivisorClass.Chern.Sheaf.TransitionCocycle.sheafMono_section_injective (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence E M).f (D.domain i ⊓ D.domain j)
  exact ((D.liftCover E M).transition_map (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M) i j).trans
    (D.difference_map i j).symm

end DolbeaultPrimitiveSystem

end

/-! Equality of actual closed Dolbeault forms is detected on a cover
of their original manifold opens. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem closedDbarForm_eq_of_local_restrictions
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]
    (U : M → Opens M) (hU : ∀ x, x ∈ U x) (a b : RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm E M)
    (h : ∀ i, DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict (show U i ≤ ⊤ from le_top) a.val =
      DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict le_top b.val) : a = b := by
  apply Subtype.ext
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  exact congrArg (fun c : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (U x.val) 1 => c.val ⟨x.val, hU x.val⟩) (h x.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition
