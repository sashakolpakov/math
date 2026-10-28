import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.ResidueFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModelResidueLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialFieldSectionDimension

/-! # Minimal Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every local minimal model of the actual dual-zero-stalk Poincare family has first free rank one. The rank is computed through actual residue-field sections of the trivial Poincare fiber and its proper smooth geometrically connected projection. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)
variable {P : Scheme.{u}} [P.IsSeparated]
variable {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ D.poincareZeroStalkScheme}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) D.poincareZeroStalkParameterMap)
variable {κ : Type u} [LinearOrder κ] [Finite κ] (U : κ → P.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
  (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
variable {C : CochainComplex (ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤)) ℕ}
variable (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
variable (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(D.poincareZeroStalkScheme, ⊤) B],
  QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareZeroStalk_minimal_firstModule_finrank_one
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) :
    Module.finrank Γ(D.poincareZeroStalkScheme, ⊤) Q.complex.X₁ = 1 := by
  have : IsLocalRing Γ(Spec (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))), ⊤) :=
    Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isLocalRing D
  let T := D.poincareZeroStalkScheme
  let t := D.poincareZeroStalkParameterMap
  let R := Γ(T, ⊤)
  let B := IsLocalRing.ResidueField R
  let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
  let : Module R B := (inferInstance : Algebra R B).toModule
  let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  let p := pullback.fst D.abelian.scheme.hom A.scheme.hom
  let HF : IsPullback (a' ≫ a) b' p (j ≫ t) := H'.paste_horiz H
  let L := D.poincare.pullback a
  obtain ⟨e⟩ := D.poincareZeroStalk_residue_family_trivial H
  obtain ⟨y, hy⟩ := D.poincareBaseFamily_exists_section (j ≫ t) HF
  have hproper : IsProper A.scheme.hom := A.proper
  have hsmooth : Smooth A.scheme.hom := inferInstance
  have hconnected : GeometricallyConnected A.scheme.hom := inferInstance
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hproper
  have : Smooth p := MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hsmooth
  have : GeometricallyConnected p := MorphismProperty.of_isPullback (P := @GeometricallyConnected)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hconnected
  have : IsProper b' := MorphismProperty.of_isPullback (P := @IsProper) HF inferInstance
  have : Smooth b' := MorphismProperty.of_isPullback (P := @Smooth) HF inferInstance
  have : GeometricallyConnected b' :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) HF inferInstance
  let q : B →+* Γ(CategoryTheory.Limits.pullback b j, ⊤) := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b')
  have hd : Module.finrank B ((Coefficient.ModulePresheaf.coefficientModulePresheaf q (L.pullback a').sheaf).obj (op ⊤)) = 1 :=
    TrivialFieldSectionDimension.properSmoothConnected_trivialModule_coefficientSections_finrank_one (K := B)
      b' y hy (L.pullback a').sheaf e
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R B) := by
    rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
    exact toAlgebra_algebraMap
  have hq : q.comp (algebraMap R B) = a'.appTop.hom.comp b.appTop.hom := by
    have hh := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficient_compatible H'
    erw [hAlg] at hh
    exact hh
  have hψ : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a' b.appTop.hom L.sheaf q hq U) 0 := by
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra j) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra j)
    have hcomparison :
        letI : Algebra R B := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra
        letI : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
        letI : Module R B := (inferInstance : Algebra R B).toModule
        ∀ hh : q.comp (algebraMap R B) = a'.appTop.hom.comp b.appTop.hom,
          QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
            Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a' b.appTop.hom L.sheaf q hh U) 0 := by
      let : Algebra R B := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra
      let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
      let : Module R B := (inferInstance : Algebra R B).toModule
      intro hh
      exact HilbertConstruction.Spec.CoefficientCechComparison.spec_affineFrame_coefficientCechModel_quasiIsoAt H' U L ha he φ 0
    erw [hAlg] at hcomparison
    exact hcomparison hq
  exact (Coefficient.ModelResidueLinearity.minimal_firstModule_finrank_eq_residue_sections
    a' b.appTop.hom L.sheaf q hq U hU φ Q).trans hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
