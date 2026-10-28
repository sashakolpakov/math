import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Normal Retraction Split -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionSplit.Constructions

noncomputable section

/-! The normal retraction splits relative pullback before the exact source-support transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem splitSourceIso_cup {C : Type*} [Category C] {Y R S T Z : C}
    (r : Y ⟶ R) (f : R ⟶ S) (s : S ≅ Y) (e : S ≅ T) (o : T ≅ Z) (g : R ⟶ T)
    (hs : r ≫ f ≫ s.hom = 𝟙 Y) (he : f ≫ e.hom = g) :
    (s.symm ≪≫ e ≪≫ o).hom = r ≫ g ≫ o.hom := by
  have hr : r ≫ f = s.inv := by
    apply (cancel_mono s.hom).mp
    rw [Category.assoc, hs, Iso.inv_hom_id]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← hr, Category.assoc, ← Category.assoc f, he]

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

theorem normalPairRelativeRetraction_split_raw (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
        (A := NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (B := (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ)
        (fun _ hx => hx) q ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)
        (A := (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) ⁻¹' NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K)
        (B := NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (fun _ hx => hx) q ≫
        (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) S q) (NormalSupportRelative.Constructions.normalPairRetractionComplement_source P hf K))).hom = 𝟙 _ := by
  have hp := NormalSupportRelative.Constructions.relativePairMap_supportEquality (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)
    (NormalSupportRelative.Constructions.normalPairRetractionComplement_source P hf K) (rfl : NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K = _)
    (fun _ hx => hx) (NormalSupportRelative.Constructions.normalPairSourceInclusion_mapsTo_retractionComplement P hf K) q
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp] at hp
  rw [hp]
  exact NormalSupportRelative.Constructions.normalPairRelativeRetraction_split P hf K q

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionSplit.Constructions
