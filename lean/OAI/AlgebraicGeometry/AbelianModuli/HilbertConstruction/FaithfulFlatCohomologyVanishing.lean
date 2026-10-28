import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FlatCohomologyBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Faithful Flat Cohomology Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulFlatCohomologyVanishing

noncomputable section

/-! Vanishing of genuine line-bundle cohomology is detected by faithfully flat affine scalar extension. Finite affine frame covers are constructed when the source is compact. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [X.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)

include H in
theorem affineFaithfullyFlatLineBundle_cohomology_vanish_iff
    [Module.FaithfullyFlat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    (n : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf n) ↔
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n) := by
  constructor
  · intro hp
    have ht : Subsingleton ((HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (Affine.TensorSectionComparison.morphismGlobalAlgebra g)).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom n).obj L.sheaf)) :=
      (Affine.FlatCohomologyBaseChange.affineFlatLineBundleCohomologyBaseChangeIso H L U hU ha he n).toLinearEquiv.toEquiv.subsingleton_congr.mpr hp
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
      Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      (N := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom n).obj L.sheaf)).mp ht
  · exact Affine.FlatCohomologyBaseChange.affineFlatLineBundle_cohomology_vanish H L U hU ha he n

include H in
theorem affineFaithfullyFlatLineBundle_cohomology_vanish_iff_of_compact
    [CompactSpace X] [Module.FaithfullyFlat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] (n : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf n) ↔
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n) := by
  obtain ⟨k, V, ha, he, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → X.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  exact affineFaithfullyFlatLineBundle_cohomology_vanish_iff H L U hU
    (fun i => ha i.down) (fun i => he i.down) n

theorem fieldExtensionLineBundle_cohomology_vanish_iff
    {k k' : Type u} [Field k] [Field k'] {X P : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    {a : P ⟶ X} {b : P ⟶ Spec (.of k')} {f : X ⟶ Spec (.of k)}
    {g : Spec (.of k') ⟶ Spec (.of k)}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (n : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf n) ↔
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let : Field Γ(Spec (.of k'), ⊤) :=
    ((Scheme.ΓSpecIso (.of k')).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k')).toField
  have : Nontrivial (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    inferInstanceAs (Nontrivial Γ(Spec (.of k'), ⊤))
  exact affineFaithfullyFlatLineBundle_cohomology_vanish_iff_of_compact H L n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulFlatCohomologyVanishing
