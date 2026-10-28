import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FlatCohomologyBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseChangeQuotientCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FlatCohomologyBaseChange

/-! # Flat Quotient Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FlatQuotientCohomology

noncomputable section

/-! A line bundle whose cohomology is a positive-degree coordinate quotient
retains this formula after any flat affine base change. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem specFlatLineBundle_cohomology_quotient
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    {B : Type u} [CommRing B] {P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Spec (.of B)} {f : X ⟶ S} {t : Spec (.of B) ⟶ S}
    (H : IsPullback a b f t) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    (hflat : let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap t).toAlgebra; Module.Flat Γ(S, ⊤) B)
    (g : ℕ) (hg : 0 < g) (I : Ideal Γ(S, ⊤))
    (hvan : ∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom q).obj L.sheaf))
    (etop : (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom g).obj L.sheaf ≅
      ModuleCat.of Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)) :
    (∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) q).obj
        (L.pullback a).sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) g).obj
      (L.pullback a).sheaf) ≅ ModuleCat.of B (B ⧸ I.map (CoefficientCechComparison.specBaseCoefficientMap t))) := by
  let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap t).toAlgebra
  let : Module.Flat Γ(S, ⊤) B := hflat
  have : Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra t) :=
    Module.Flat.of_linearEquiv (CoefficientCechComparison.specBaseCoefficientEquiv t).toLinearEquiv.symm
  constructor
  · intro q hq
    have hz : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf q) :=
      ModuleCat.isZero_iff_subsingleton.mp (hvan q hq)
    have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf q) :=
      Affine.FlatCohomologyBaseChange.affineFlatLineBundle_cohomology_vanish H L U hU ha he q hz
    have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) q).obj (L.pullback a).sheaf) :=
      inferInstanceAs (Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf q))
    exact ModuleCat.isZero_of_subsingleton _
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
    exact ⟨(FlatCohomologyBaseChange.specFlatLineBundleCohomologyBaseChangeIso H L U hU ha he hflat n).symm ≪≫
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).mapIso etop ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.toModuleIso⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FlatQuotientCohomology
