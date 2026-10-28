import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Flat Cohomology Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FlatCohomologyBaseChange

noncomputable section

/-! Genuine cohomology of a line bundle commutes with a flat affine change of scalars in every degree, on a finite affine frame cover. Over a field this applies to every affine base change. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [X.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

def affineFlatLineBundleCohomologyBaseChangeIso
    [Module.Flat Γ(S, ⊤) (TensorSectionComparison.morphismGlobalAlgebra g)] (n : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (TensorSectionComparison.morphismGlobalAlgebra g)).obj
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom n).obj L.sheaf) ≅
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (a.appTop.hom.comp f.appTop.hom)
      n).obj (L.pullback a).sheaf := by
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : (L.pullback a).sheaf.IsQuasicoherent := (L.pullback a).isQuasicoherent
  have : IsAffineHom a :=
    isAffineHom_isStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) :=
    Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U ha he
  exact (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (TensorSectionComparison.morphismGlobalAlgebra g)).mapIso
      (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso f.appTop.hom L.sheaf U hU ha n).symm ≪≫
    HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor.flatHomologyIso (TensorSectionComparison.morphismGlobalAlgebra g)
      (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) n ≪≫
    HomologicalComplex.homologyMapIso (asIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U)) n ≪≫
    OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso (a.appTop.hom.comp f.appTop.hom) (L.pullback a).sheaf
      (fun i => a ⁻¹ᵁ U i) (PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU)
      (fun i => (ha i).preimage a) n

include H U hU ha he in
theorem affineFlatLineBundle_cohomology_vanish
    [Module.Flat Γ(S, ⊤) (TensorSectionComparison.morphismGlobalAlgebra g)] (n : ℕ)
    (hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf n) := by
  let : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom
    n).obj L.sheaf) := hL
  change Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (a.appTop.hom.comp f.appTop.hom) n).obj (L.pullback a).sheaf)
  apply ModuleCat.subsingleton_of_isZero
  exact (affineFlatLineBundleCohomologyBaseChangeIso H L U hU ha he n).isZero_iff.mp
    ((HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (TensorSectionComparison.morphismGlobalAlgebra g)).map_isZero
      (ModuleCat.isZero_of_subsingleton _))

theorem fieldAffineLineBundle_cohomology_vanish
    {k : Type u} [Field k] {X Y P : Scheme.{u}} [X.IsSeparated] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    (n : ℕ) (hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf n) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  exact affineFlatLineBundle_cohomology_vanish H L U hU ha he n hL

theorem fieldAffineLineBundle_cohomology_vanish_of_compact
    {k : Type u} [Field k] {X Y P : Scheme.{u}} [X.IsSeparated] [CompactSpace X] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    (n : ℕ) (hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf n) := by
  obtain ⟨r, V, ha, he, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin r) → X.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  exact fieldAffineLineBundle_cohomology_vanish H L U hU
    (fun i => ha i.down) (fun i => he i.down) n hL

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FlatCohomologyBaseChange
