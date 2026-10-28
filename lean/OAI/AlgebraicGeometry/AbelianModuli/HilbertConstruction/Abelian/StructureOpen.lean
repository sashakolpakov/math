import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.OneDimensionOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ModelPositiveCohomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Structure Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! A projective abelian family over an affine Noetherian base has an
actual open on which the first structure-sheaf cohomology has a prescribed
dimension bound. Its field-point criterion uses the original pullback
family and genuine coefficient cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def Schemes.AbelianScheme.structureH1Dimension {K : Type u} [Field K] {g : ℕ}
    (A : Schemes.AbelianScheme g (Spec (.of K))) : ℕ :=
  Module.finrank Γ(Spec (.of K), ⊤)
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor A.scheme.hom.appTop.hom 1).obj
      (Line.Bundles.structureModule A.scheme.left))

theorem Schemes.AbelianScheme.exists_structureH1Open
    {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (A : Schemes.AbelianScheme g S) (P : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (d : ℕ) :
    ∃ V : S.Opens, ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S),
      Set.range b ⊆ (V : Set S) ↔ (A.pullback b).structureH1Dimension ≤ d := by
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let : A.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.scheme.hom]
    infer_instance⟩
  let U := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover A.scheme P
  have hU : iSup U = ⊤ := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers A.scheme P
  have ha : ∀ i, IsAffineOpen (U i) := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.affine A.scheme P
  let L := Line.Bundles.LineBundle.trivial A.scheme.left
  have he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
      Line.Bundles.structureModule (U i).toScheme) := fun i => ⟨Line.Bundles.structureModulePullbackIso (U i).ι⟩
  obtain ⟨C, φ, _, _, hfin, hproj, hgeo⟩ :=
    ProperFlat.GeometricCechModel.properFlat_exists_geometric_cech_model A.scheme.hom L U hU ha he
  let : Module.Finite Γ(S, ⊤) (C.X 0) := hfin 0
  let : Module.Finite Γ(S, ⊤) (C.X 1) := hfin 1
  let : Module.Finite Γ(S, ⊤) (C.X 2) := hfin 2
  let : Module.Projective Γ(S, ⊤) (C.X 0) := hproj 0
  let : Module.Projective Γ(S, ⊤) (C.X 1) := hproj 1
  let : Module.Projective Γ(S, ⊤) (C.X 2) := hproj 2
  refine ⟨Cochain.OneDimensionOpen.cochainOneDimensionOpen C d, ?_⟩
  intro K _ b
  let : Algebra Γ(S, ⊤) Γ(Spec (.of K), ⊤) := b.appTop.hom.toAlgebra
  let a := pullback.fst A.scheme.hom b
  let p := pullback.snd A.scheme.hom b
  let H : IsPullback a p A.scheme.hom b := IsPullback.of_hasPullback A.scheme.hom b
  let : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra b) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) :=
    hgeo (Spec (.of K)) (CategoryTheory.Limits.pullback A.scheme.hom b) a p b H
  let e := Geometric.ModelPositiveCohomology.geometricModelPositiveCohomologyLinearEquiv H L U hU ha φ 0
  let eO := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor p.appTop.hom 1).mapIso
    (Line.Bundles.structureModulePullbackIso a)
  have hdim : Module.finrank Γ(Spec (.of K), ⊤)
      ((Cochain.ScalarExtensionKernel.cochainScalarExtension C Γ(Spec (.of K), ⊤)).homology 1) =
        (A.pullback b).structureH1Dimension :=
    e.finrank_eq.trans eO.toLinearEquiv.finrank_eq
  exact (Cochain.OneDimensionOpen.cochainOneDimensionOpen_field_point C b d).trans
    (congrArg (fun n : ℕ => n ≤ d) hdim).to_iff

def Schemes.AbelianScheme.structureH1Open
    {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (A : Schemes.AbelianScheme g S) (P : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (d : ℕ) : S.Opens :=
  (A.exists_structureH1Open P d).choose

theorem Schemes.AbelianScheme.structureH1Open_field_point
    {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (A : Schemes.AbelianScheme g S) (P : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (d : ℕ)
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S) :
    Set.range b ⊆ (A.structureH1Open P d : Set S) ↔
      (A.pullback b).structureH1Dimension ≤ d :=
  (A.exists_structureH1Open P d).choose_spec K b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
