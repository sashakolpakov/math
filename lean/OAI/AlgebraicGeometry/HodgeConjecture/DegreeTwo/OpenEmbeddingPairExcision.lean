import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension

/-! # Open Embedding Pair Excision -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingPairExcision.Constructions

noncomputable section

/-! Excision for an actual open embedding written with the specified pair complements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
variable (A : Set X) (B : Set Y) (hB : IsOpen B) (hpre : f ⁻¹' B = A)
variable (hcover : Bᶜ ⊆ Set.range f)

include hpre in
theorem openEmbeddingPair_support_eq : (f ⁻¹' Bᶜ)ᶜ = A := by
  rw [Set.preimage_compl, compl_compl, hpre]

include hpre in
theorem openEmbeddingPair_mapsTo : Set.MapsTo f A B := by
  intro x hx
  have hx' : x ∈ f ⁻¹' B := by rw [hpre]; exact hx
  exact hx'

def openEmbeddingPairCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n :=
  eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y S n)
    (compl_compl B).symm) ≪≫
    OpenEmbeddingExtension.Constructions.openEmbeddingSupportCohomologyIso f hf Bᶜ hB.isClosed_compl hcover n ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n)
      (openEmbeddingPair_support_eq f A B hpre))

theorem relativeCohomologyMap_domainComplementCast {A : Set X} {B B' : Set Y}
    (h : B = B') (hm : Set.MapsTo f A B) (hm' : Set.MapsTo f A B') (n : ℕ) :
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y S n) h) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm' n =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm n := by
  subst B'
  exact Category.id_comp _

theorem openEmbeddingPairCohomologyIso_hom (n : ℕ) :
    (openEmbeddingPairCohomologyIso f hf A B hB hpre hcover n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (openEmbeddingPair_mapsTo f A B hpre) n := by
  rw [openEmbeddingPairCohomologyIso, Iso.trans_hom, Iso.trans_hom,
    OpenEmbeddingExtension.Constructions.openEmbeddingSupportCohomologyIso_hom]
  have hm : Set.MapsTo f A Bᶜᶜ := by
    simpa only [compl_compl] using openEmbeddingPair_mapsTo f A B hpre
  have hcast := OpenEmbeddingExtension.Constructions.relativeCohomologyMap_codomainComplementCast f
    (openEmbeddingPair_support_eq f A B hpre) (fun _ hx => hx) hm n
  exact (congrArg
    (fun u => eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y S n)
      (compl_compl B).symm) ≫ u) hcast).trans
    (relativeCohomologyMap_domainComplementCast f (compl_compl B).symm
      (openEmbeddingPair_mapsTo f A B hpre) hm n)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingPairExcision.Constructions
