import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSourceSheafComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget
import OAI.AlgebraicTopology.Duality.Poincare.CapRelativeTrace
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OrdinaryHomeomorphCohomology

/-! # Normal Ordinary Thom Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalOrdinaryThomIso.Constructions

noncomputable section

/-! On a normal neighborhood, the actual Thom class cups ordinary cohomology isomorphically onto support cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology OAI.AlgebraicTopology.Duality.Poincare.CapRelativeTrace

set_option backward.isDefEq.respectTransparency false

theorem relativeCohomologyIdentity_of_eq (X : TopCat.{0}) {A B : Set X} (h : A=B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X)
        (A := A) (B := B) (fun _ hx => h ▸ hx) n =
      eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) h.symm) := by
  subst B
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id]
  rfl

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

theorem normalPairSourceInclusion_tangent :
    NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf ≫ NormalPairProductSupport.Constructions.normalPairTangentMap P =
      (TopCat.isoOfHomeo (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf)).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  exact congrArg Prod.snd (NormalPairSourceSupport.Constructions.normalPairSourceInclusion_coordinates P hf y)

def normalPairTangentOrdinaryCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) n ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) n :=
  OrdinaryHomeomorphCohomology.Constructions.rationalCohomologyIsoOfTopologicalIso
    (TopCat.isoOfHomeo (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf)) n ≪≫
      (NormalSourceSheafComparison.Constructions.normalPairSourceOrdinaryCohomologyIso P hf n).symm

theorem normalPairTangentOrdinaryCohomologyIso_hom (n : ℕ) :
    (normalPairTangentOrdinaryCohomologyIso P hf n).hom =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P) n := by
  apply (cancel_mono (NormalSourceSheafComparison.Constructions.normalPairSourceOrdinaryCohomologyIso P hf n).hom).mp
  simp only [normalPairTangentOrdinaryCohomologyIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback _ _ _ =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback _ _ _ ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback _ _ _
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp, normalPairSourceInclusion_tangent]

theorem normalPairCombinedComplement_empty :
    NormalPairProductSupport.Constructions.normalPairCombinedComplement P ∅ = P.relativeComplement := by
  let _ := (inferInstance : TopologicalSpace M)
  simp only [NormalPairProductSupport.Constructions.normalPairCombinedComplement, Set.preimage_empty, Set.union_empty]

def normalPairEmptySupportForget (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
        (NormalPairProductSupport.Constructions.normalPairCombinedComplement P ∅) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) P.relativeComplement n :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of P.neighborhood))
    (A := P.relativeComplement) (B := NormalPairProductSupport.Constructions.normalPairCombinedComplement P ∅) Set.subset_union_left n

instance normalPairEmptySupportForget_isIso (n : ℕ) : IsIso (normalPairEmptySupportForget P n) := by
  have he := relativeCohomologyIdentity_of_eq (TopCat.of P.neighborhood)
    (normalPairCombinedComplement_empty P).symm n
  change IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of P.neighborhood))
    (A := P.relativeComplement) (B := NormalPairProductSupport.Constructions.normalPairCombinedComplement P ∅) Set.subset_union_left n)
  rw [he]
  infer_instance

def normalPairTangentRelativeEmptyIso (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) ∅ q ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) q :=
  AlgebraicTopology.Duality.Poincare.CapRelativeTrace.relativeEmptyCohomologyIso (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) q ≪≫
    normalPairTangentOrdinaryCohomologyIso P hf q

theorem normalPairEmptyThom_factor (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) ∅ q) :
    normalPairEmptySupportForget P (2*c+q) (PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P ∅ isOpen_empty q a) =
      CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood) P.relativeComplement (2*c) q
        P.rationalClassFin ((normalPairTangentRelativeEmptyIso P hf q).hom a) := by
  rw [PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso_eq_cup]
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _ (𝟙 (TopCat.of P.neighborhood)) _ _
    (SupportCup.Constructions.twoSupportCohomologyCup _ _ _ _ _ _ _ _ _) = _
  rw [SupportCupForget.Constructions.twoSupportCohomologyCup_forget_right]
  apply congrArg (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood)
    P.relativeComplement (2*c) q P.rationalClassFin)
  change _ = (normalPairTangentOrdinaryCohomologyIso P hf q).hom
    ((AlgebraicTopology.Duality.Poincare.CapRelativeTrace.relativeEmptyCohomologyIso (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) q).hom a)
  rw [normalPairTangentOrdinaryCohomologyIso_hom]
  exact ConcreteCategory.congr_hom (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ)
    (NormalPairProductSupport.Constructions.normalPairTangentMap P) (B := NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' ∅) (B' := ∅) (fun _ hx => hx) q) a

def normalPairOrdinaryThomIso (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) q ≃ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) P.relativeComplement (2*c+q) :=
  (normalPairTangentRelativeEmptyIso P hf q).symm.toLinearEquiv.trans
    ((PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P ∅ isOpen_empty q).trans
      (asIso (normalPairEmptySupportForget P (2*c+q))).toLinearEquiv)

theorem normalPairOrdinaryThomIso_eq_cup (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) q) :
    normalPairOrdinaryThomIso P hf q b =
      CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood) P.relativeComplement (2*c) q
        P.rationalClassFin b := by
  change normalPairEmptySupportForget P (2*c+q)
    (PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P ∅ isOpen_empty q
      ((normalPairTangentRelativeEmptyIso P hf q).inv b)) = _
  rw [normalPairEmptyThom_factor P hf, Iso.inv_hom_id_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalOrdinaryThomIso.Constructions
