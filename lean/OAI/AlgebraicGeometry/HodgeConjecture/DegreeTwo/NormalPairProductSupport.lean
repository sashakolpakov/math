import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenNormal
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Normal Pair Product Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions

noncomputable section

section

/-!
# DegreeTwo: actual normal-pair coordinates with arbitrary tangential support

The original normal-pair homeomorphism is reordered to put the normal
factor first. The removed subspaces are the literal image complement and
the actual inverse image of the tangential complement.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles

set_option backward.isDefEq.respectTransparency false

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

abbrev normalPairTangentSpace := Metric.ball (0 : E) P.radius

abbrev normalPairNormalOpen : Opens (Fin c → ℂ) := ⟨Metric.ball 0 P.radius,Metric.isOpen_ball⟩

abbrev normalPairNormalOrigin : normalPairNormalOpen P := ⟨0,Metric.mem_ball_self P.radius_pos⟩

def normalPairFirstHomeomorph : P.neighborhood ≃ₜ (normalPairNormalOpen P × normalPairTangentSpace P) :=
  P.homeomorph.trans (Homeomorph.prodComm _ _)

def normalPairFirstMap : TopCat.of P.neighborhood ⟶ TopCat.of (normalPairNormalOpen P × normalPairTangentSpace P) :=
  (TopCat.isoOfHomeo (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (normalPairNormalOpen P × normalPairTangentSpace P)) (normalPairFirstHomeomorph P)).hom

def normalPairTangentMap : TopCat.of P.neighborhood ⟶ TopCat.of (normalPairTangentSpace P) :=
  normalPairFirstMap P ≫ CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection (normalPairNormalOpen P) (normalPairTangentSpace P)

theorem normalPairFirstMap_complement (y : P.neighborhood) :
    y ∈ P.relativeComplement ↔
      normalPairFirstMap P y ∈ Prod.fst ⁻¹' ({normalPairNormalOrigin P}ᶜ : Set (normalPairNormalOpen P)) := by
  let _ := (inferInstance : NormedSpace ℝ E)
  exact P.homeomorph_mem_relativeComplement y

theorem normalPair_relativeComplement_isOpen : IsOpen P.relativeComplement := by
  have he : P.relativeComplement = normalPairFirstMap P ⁻¹'
      (Prod.fst ⁻¹' ({normalPairNormalOrigin P}ᶜ : Set (normalPairNormalOpen P))) :=
    Set.ext (normalPairFirstMap_complement P)
  rw [he]
  have hN : IsOpen ({normalPairNormalOrigin P}ᶜ : Set (normalPairNormalOpen P)) :=
    isClosed_singleton.isOpen_compl
  exact (hN.preimage continuous_fst).preimage (normalPairFirstMap P).hom.continuous

def normalPairCombinedComplement (B : Set (normalPairTangentSpace P)) : Set P.neighborhood :=
  P.relativeComplement ∪ normalPairTangentMap P ⁻¹' B

theorem normalPairFirstMap_combinedComplement (B : Set (normalPairTangentSpace P)) (y : P.neighborhood) :
    y ∈ normalPairCombinedComplement P B ↔
      normalPairFirstMap P y ∈ RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (normalPairNormalOpen P))
        (TopCat.of (normalPairTangentSpace P)) ({normalPairNormalOrigin P}ᶜ) B := by
  exact or_congr (normalPairFirstMap_complement P y) Iff.rfl

def normalPairProductCohomologyIso (B : Set (normalPairTangentSpace P)) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (normalPairNormalOpen P × normalPairTangentSpace P))
      (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (normalPairNormalOpen P))
        (TopCat.of (normalPairTangentSpace P)) ({normalPairNormalOrigin P}ᶜ) B) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (normalPairCombinedComplement P B) n :=
  AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (normalPairNormalOpen P × normalPairTangentSpace P))
    (normalPairFirstHomeomorph P) (normalPairCombinedComplement P B)
    (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (normalPairNormalOpen P))
      (TopCat.of (normalPairTangentSpace P)) ({normalPairNormalOrigin P}ᶜ) B)
    (normalPairFirstMap_combinedComplement P B) n

theorem normalPairProductCohomologyIso_hom (B : Set (normalPairTangentSpace P)) (n : ℕ) :
    (normalPairProductCohomologyIso P B n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalPairFirstMap P)
        (fun y hy => (normalPairFirstMap_combinedComplement P B y).mp hy) n := rfl

end

/-! The actual embedded source in a normal neighborhood is the tangent ball. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N E F : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
variable (hf : Topology.IsEmbedding f)

abbrev normalPairTangentBallOpen : Opens E := ⟨Metric.ball 0 P.radius,Metric.isOpen_ball⟩

abbrev normalPairSourceOpen : Opens M :=
  ⟨f ⁻¹' P.neighborhood, P.isOpen_neighborhood.preimage hf.continuous⟩

def normalPairSourceToNeighborhood (y : normalPairSourceOpen P hf) : P.neighborhood :=
  ⟨f y.val,y.property⟩

def normalPairSourceToTangent (y : normalPairSourceOpen P hf) : normalPairTangentBallOpen P :=
  (P.homeomorph (normalPairSourceToNeighborhood P hf y)).1

theorem normalPairSource_normal_zero (y : normalPairSourceOpen P hf) :
    (P.homeomorph (normalPairSourceToNeighborhood P hf y)).2 =
      ⟨0,Metric.mem_ball_self P.radius_pos⟩ := by
  apply Subtype.ext
  exact (P.mem_range_iff (normalPairSourceToNeighborhood P hf y)).mp ⟨y.val,rfl⟩

theorem normalPairSourceToTangent_bijective : Function.Bijective (normalPairSourceToTangent P hf) := by
  constructor
  · intro y z h
    apply Subtype.ext
    apply hf.injective
    have hP : P.homeomorph (normalPairSourceToNeighborhood P hf y) =
        P.homeomorph (normalPairSourceToNeighborhood P hf z) :=
      Prod.ext h ((normalPairSource_normal_zero P hf y).trans (normalPairSource_normal_zero P hf z).symm)
    exact congrArg Subtype.val (P.homeomorph.injective hP)
  · intro t
    let z : P.neighborhood := P.homeomorph.symm (t,⟨0,Metric.mem_ball_self P.radius_pos⟩)
    have hz : z.val ∈ Set.range f := by
      apply (P.mem_range_iff z).mpr
      have h := congrArg (fun w => w.2.val) (P.homeomorph.apply_symm_apply
        (t,⟨0,Metric.mem_ball_self P.radius_pos⟩))
      exact h
    obtain ⟨y,hy⟩ := hz
    have hyP : f y ∈ P.neighborhood := hy ▸ z.property
    refine ⟨⟨y,hyP⟩,?_⟩
    have hyz : normalPairSourceToNeighborhood P hf ⟨y,hyP⟩ = z := Subtype.ext hy
    unfold normalPairSourceToTangent
    rw [hyz]
    exact congrArg Prod.fst (P.homeomorph.apply_symm_apply _)

theorem continuous_normalPairSourceToTangent : Continuous (normalPairSourceToTangent P hf) :=
  continuous_fst.comp (P.homeomorph.continuous.comp
    ((hf.continuous.comp continuous_subtype_val).subtype_mk _))

def normalPairSourceHomeomorph : normalPairSourceOpen P hf ≃ₜ normalPairTangentBallOpen P := by
  let e := Equiv.ofBijective (normalPairSourceToTangent P hf) (normalPairSourceToTangent_bijective P hf)
  refine { toEquiv := e
           continuous_toFun := continuous_normalPairSourceToTangent P hf
           continuous_invFun := ?_ }
  apply ((hf.comp Topology.IsEmbedding.subtypeVal).isInducing.continuous_iff).mpr
  have he : (f ∘ Subtype.val) ∘ e.symm =
      fun t => (P.homeomorph.symm (t,⟨0,Metric.mem_ball_self P.radius_pos⟩)).val := by
    funext t
    have hP : P.homeomorph (normalPairSourceToNeighborhood P hf (e.symm t)) =
        (t,⟨0,Metric.mem_ball_self P.radius_pos⟩) :=
      Prod.ext (e.apply_symm_apply t) (normalPairSource_normal_zero P hf (e.symm t))
    have hz := congrArg P.homeomorph.symm hP
    rw [P.homeomorph.symm_apply_apply] at hz
    exact congrArg Subtype.val hz
  change Continuous ((f ∘ Subtype.val) ∘ e.symm)
  rw [he]
  exact continuous_subtype_val.comp (P.homeomorph.symm.continuous.comp
    (continuous_id.prodMk continuous_const))

theorem normalPairSourceHomeomorph_apply (y : normalPairSourceOpen P hf) :
    normalPairSourceHomeomorph P hf y = normalPairSourceToTangent P hf y := rfl

theorem normalPairSourceHomeomorph_inverse_inclusion (t : normalPairTangentBallOpen P) :
    f ((normalPairSourceHomeomorph P hf).symm t).val =
      (P.homeomorph.symm (t,⟨0,Metric.mem_ball_self P.radius_pos⟩)).val := by
  have hP : P.homeomorph (normalPairSourceToNeighborhood P hf ((normalPairSourceHomeomorph P hf).symm t)) =
      (t,⟨0,Metric.mem_ball_self P.radius_pos⟩) :=
    Prod.ext ((normalPairSourceHomeomorph P hf).apply_symm_apply t)
      (normalPairSource_normal_zero P hf _)
  have hz := congrArg P.homeomorph.symm hP
  rw [P.homeomorph.symm_apply_apply] at hz
  exact congrArg Subtype.val hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions
