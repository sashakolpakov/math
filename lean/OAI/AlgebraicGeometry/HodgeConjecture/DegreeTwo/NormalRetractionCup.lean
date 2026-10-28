import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Normal Retraction Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionCup.Constructions

noncomputable section

/-! The previously constructed normal-chart Gysin map is cup with the normal class and actual source retraction pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem twoSupportCup_rightSupportEquality_output (X : TopCat.{0}) (C : Set X)
    {A B S : Set X} (h : A = B) (eA : C ∪ A = S) (eB : C ∪ B = S)
    (hC : IsOpen C) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A q) :
    (eqToIso (congrArg (fun T => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X T (p+q)) eA)).hom
      (SupportCup.Constructions.twoSupportCohomologyCup X C A hC hA p q a b) =
    (eqToIso (congrArg (fun T => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X T (p+q)) eB)).hom
      (SupportCup.Constructions.twoSupportCohomologyCup X C B hC hB p q a
        ((eqToIso (congrArg (fun T => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X T q) h)).hom b)) := by
  subst B
  rfl

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

theorem normalPairRetraction_supported_pullback (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q : ℕ) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K q).inv ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P)
        (A := (NormalPairProductSupport.Constructions.normalPairTangentMap P) ⁻¹' (SourceSupportedThomIso.Constructions.normalPairSourceTangentCompact P hf K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ)
        (B := (SourceSupportedThomIso.Constructions.normalPairSourceTangentCompact P hf K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ) (fun _ hx => hx) q =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
        (A := NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (B := (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ)
        (fun _ hx => hx) q ≫
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of P.neighborhood) S q) (NormalSupportRelative.Constructions.normalPairRetractionComplement_eq_tangent P hf K))).hom := by
  rw [SupportedCupTransport.Constructions.compactHomeomorphStage_inv_eq_pullback, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  have he := NormalSupportRelative.Constructions.relativePairMap_supportEquality (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
    (NormalSupportRelative.Constructions.normalPairRetractionComplement_eq_tangent P hf K) (rfl : (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ = _)
    (fun _ hx => hx)
    (fun _ hy => SupportedCupTransport.Constructions.compactHomeomorph_inverse_mapsTo
      (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K hy) q
  simpa only [eqToIso_refl, Iso.refl_hom, Category.id_comp, SourceThomProjection.Constructions.normalPairSourceRetractionMap] using he.symm

variable [T2Space M]

theorem normalPairSourceSupportedCohomologyIso_eq_retraction_cup
    (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
      (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q) :
    SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K q b =
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of P.neighborhood) S (2*c+q)) (NormalSupportRelative.Constructions.normalPairRetraction_union_complement P hf K))).hom
        (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of P.neighborhood) P.relativeComplement
          (NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P)
          (NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P hf K).isOpen (2*c) q P.rationalClassFin
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
            (A := NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (B := (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ)
            (fun _ hx => hx) q b)) := by
  rw [SourceThomProjection.Constructions.normalPairSourceSupportedCohomologyIso_eq, PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso_eq_cup]
  have hp := ConcreteCategory.congr_hom (normalPairRetraction_supported_pullback P hf K q) b
  simp only [ConcreteCategory.comp_apply] at hp
  erw [hp]
  exact (twoSupportCup_rightSupportEquality_output (TopCat.of P.neighborhood) P.relativeComplement
    (NormalSupportRelative.Constructions.normalPairRetractionComplement_eq_tangent P hf K)
    (NormalSupportRelative.Constructions.normalPairRetraction_union_complement P hf K) (SourceSupportedThomIso.Constructions.normalPairSourceComplement_eq P hf K)
    (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P hf K).isOpen
    ((SourceSupportedThomIso.Constructions.normalPairSourceTangentCompact P hf K).isCompact.isClosed.isOpen_compl.preimage
      (NormalPairProductSupport.Constructions.normalPairTangentMap P).hom.continuous) (2*c) q P.rationalClassFin
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
      (A := NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (B := (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ)
      (fun _ hx => hx) q b)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionCup.Constructions
