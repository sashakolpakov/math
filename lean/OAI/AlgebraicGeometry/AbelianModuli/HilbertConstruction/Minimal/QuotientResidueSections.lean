import Mathlib.AlgebraicGeometry.Fiber
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.QuotientSectionSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorCoefficientSurjectivity

/-! # Quotient Residue Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.QuotientResidueSections

noncomputable section

/-! Quotienting by the coefficients of the actual minimal first differential gives surjectivity of the native residue-fiber section comparison. The quotient and residue coefficient maps, their scalar tower, and the geometric model comparisons are derived from the actual affine schemes. -/
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem minimal_quotient_residue_sectionTensor_surjective
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated] [IsLocalRing Γ(S, ⊤)]
    (f : X ⟶ S) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U)
    (ht : ∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2)) :
    let I := Q.firstDifferentialIdeal
    let t := Affine.QuotientCoefficientMap.affineCoordinateMap (S := S) (Ideal.Quotient.mk I)
    let b := pullback.snd f t
    ∀ x : Spec (.of (Γ(S, ⊤) ⧸ I)),
      Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison
        (IsPullback.of_hasPullback b ((Spec (.of (Γ(S, ⊤) ⧸ I))).fromSpecResidueField x))
        (L.pullback (pullback.fst f t)).sheaf).app (op ⊤)) := by
  let R := Γ(S, ⊤)
  let I : Ideal R := Q.firstDifferentialIdeal
  let B := R ⧸ I
  let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
  let : Module R B := Algebra.toModule
  let T := Spec (.of B)
  let t : T ⟶ S := Affine.QuotientCoefficientMap.affineCoordinateMap (Ideal.Quotient.mk I)
  let Y := pullback f t
  let g : Y ⟶ X := pullback.fst f t
  let b : Y ⟶ T := pullback.snd f t
  let HB : IsPullback g b f t := IsPullback.of_hasPullback f t
  change ∀ x : T, Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison
    (IsPullback.of_hasPullback b (T.fromSpecResidueField x)) (L.pullback g).sheaf).app (op ⊤))
  intro x
  let C := T.residueField x
  let j : Spec C ⟶ T := T.fromSpecResidueField x
  let P := b.fiber x
  let a : P ⟶ Y := b.fiberι x
  let c : P ⟶ Spec C := b.fiberToSpecResidueField x
  let HC : IsPullback a c b j := IsPullback.of_hasPullback b j
  let HD : IsPullback (a ≫ g) c f (j ≫ t) := HC.paste_horiz HB
  let : Algebra B C := (HilbertConstruction.Spec.CoefficientComposition.specCoordinateRingMap j).toAlgebra
  let : Algebra R C := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap (j ≫ t)).toAlgebra
  let : Algebra Γ(S, ⊤) (IsLocalRing.ResidueField (T.presheaf.stalk x)) :=
    (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap (j ≫ t)).toAlgebra
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap t).toAlgebra = (inferInstance : Algebra R B) :=
    Affine.QuotientCoefficientMap.affineQuotientCoefficientAlgebra_eq I
  have hm : HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap t = algebraMap R B :=
    Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap (Ideal.Quotient.mk I)
  have : IsScalarTower R B C := by
    apply IsScalarTower.of_algebraMap_eq'
    exact ((congrArg (fun q : R →+* B => (HilbertConstruction.Spec.CoefficientComposition.specCoordinateRingMap j).comp q) hm.symm).trans
      (HilbertConstruction.Spec.CoefficientComposition.specCoordinateRingMap_comp j t)).symm
  let qB : B →+* Γ(Y, ⊤) := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b)
  let qC : C →+* Γ(P, ⊤) := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := c)
  have hqB : qB.comp (algebraMap R B) = g.appTop.hom.comp f.appTop.hom := by
    have hh := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficient_compatible HB
    change qB.comp (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap t) = g.appTop.hom.comp f.appTop.hom at hh
    exact (congrArg (fun q : R →+* B => qB.comp q) hm.symm).trans hh
  have hqC : qC.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f.appTop.hom :=
    HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficient_compatible HD
  have hα : qC.comp (algebraMap B C) = a.appTop.hom.comp qB :=
    HilbertConstruction.Spec.CoefficientComposition.specPullbackCoefficient_refinement a b c j HC.w
  have hB : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f.appTop.hom L.sheaf qB hqB U) 0 := by
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra t) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra t)
    have hcomparison := HilbertConstruction.Spec.CoefficientCechComparison.spec_affineFrame_coefficientCechModel_quasiIsoAt HB U L ha he φ 0
    let property (alg : Algebra R B) : Prop :=
      letI : Algebra R B := alg
      letI : Module R B := Algebra.toModule
      ∀ hq : qB.comp (algebraMap R B) = g.appTop.hom.comp f.appTop.hom,
        QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
          Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f.appTop.hom L.sheaf qB hq U) 0
    have hp : property (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap t).toAlgebra := by
      intro hq
      exact hcomparison
    have hp' : property (inferInstance : Algebra R B) := hAlg ▸ hp
    exact hp' hqB
  have hC : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (a ≫ g) f.appTop.hom L.sheaf qC hqC U) 0 := by
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (j ≫ t)) φ) :=
      ht (Affine.TensorSectionComparison.morphismGlobalAlgebra (j ≫ t))
    exact HilbertConstruction.Spec.CoefficientCechComparison.spec_affineFrame_coefficientCechModel_quasiIsoAt HD U L ha he φ 0
  have hsurj : Function.Surjective (algebraMap R B) := by
    simpa only [Ideal.Quotient.algebraMap_eq] using! (Ideal.Quotient.mk_surjective (I := I))
  have hQ : Q.complex.f.hom.baseChange B = 0 := Q.firstDifferential_quotient_zero
  have hs := QuotientSectionSurjectivity.minimal_quotient_sectionTensor_surjective
    a g f.appTop.hom L.sheaf qB qC hqB hqC U hsurj hU hα φ Q hQ
  exact Section.TensorCoefficientSurjectivity.cartesian_sectionTensor_surjective_of_spec_pairing HC (L.pullback g).sheaf
    (g.appTop.hom.comp f.appTop.hom)
    (Iterated.SectionTensorValues.sectionTensor_composite_coefficients a g f.appTop.hom qC hqC) hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.QuotientResidueSections
