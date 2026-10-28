import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorCoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Coefficient Cech Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientCechComparison

noncomputable section

/-! The coordinate ring of an affine test scheme is identified with its actual global functions. This transports the genuine Cartesian Cech comparison to the coordinate ring, with the coefficient action determined by the scheme morphism itself. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {B : Type u} [CommRing B]

def specBaseCoefficientMap (g : Spec (.of B) ⟶ S) : Γ(S, ⊤) →+* B :=
  (Scheme.ΓSpecIso (.of B)).hom.hom.comp g.appTop.hom

def specBaseCoefficientEquiv (g : Spec (.of B) ⟶ S) :
    letI : Algebra Γ(S, ⊤) B := (specBaseCoefficientMap g).toAlgebra
    B ≃ₐ[Γ(S, ⊤)] Affine.TensorSectionComparison.morphismGlobalAlgebra g := by
  letI : Algebra Γ(S, ⊤) B := (specBaseCoefficientMap g).toAlgebra
  refine { (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm with commutes' := ?_ }
  intro x
  change (Scheme.ΓSpecIso (.of B)).inv ((Scheme.ΓSpecIso (.of B)).hom (g.appTop x)) = g.appTop x
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of B)).hom_inv_id (g.appTop x)

theorem specBaseCoefficientMap_surjective [IsAffine S]
    (g : Spec (.of B) ⟶ S) [IsClosedImmersion g] : Function.Surjective (specBaseCoefficientMap g) :=
  (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.surjective.comp
    (IsClosedImmersion.isAffine_surjective_of_isAffine g).2

variable {X P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Spec (.of B)}
variable {f : X ⟶ S} {g : Spec (.of B) ⟶ S} (H : IsPullback a b f g)

def specPullbackCoefficientMap : B →+* Γ(P, ⊤) :=
  b.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom

include H in
theorem specPullbackCoefficient_compatible :
    letI : Algebra Γ(S, ⊤) B := (specBaseCoefficientMap g).toAlgebra
    (specPullbackCoefficientMap (b := b)).comp (algebraMap Γ(S, ⊤) B) = a.appTop.hom.comp f.appTop.hom := by
  let : Algebra Γ(S, ⊤) B := (specBaseCoefficientMap g).toAlgebra
  ext x
  exact (congrArg b.appTop ((specBaseCoefficientEquiv g).commutes x)).trans
    (DFunLike.congr_fun (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) x)

variable (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem spec_coefficientCechModel_quasiIsoAt
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U) (n : ℕ)
    [hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H M U) n] :
    letI : Algebra Γ(S, ⊤) B := (specBaseCoefficientMap g).toAlgebra
    QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f.appTop.hom M (specPullbackCoefficientMap (b := b))
        (specPullbackCoefficient_compatible H) U) n := by
  let : Algebra Γ(S, ⊤) B := (specBaseCoefficientMap g).toAlgebra
  let K := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U
  let E := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
  let u : Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) D ⟶
      Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) K :=
    Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ
  let v : Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) K ⟶ E :=
    Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H M U
  let w : Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) K ⟶ E :=
    Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a f.appTop.hom M
      b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) U
  have he : v = w := rfl
  have hv : QuasiIsoAt (u ≫ v) n := hψ
  have hw : QuasiIsoAt (u ≫ w) n :=
    (congrArg (fun z : Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) K ⟶ E =>
      QuasiIsoAt (u ≫ z) n) he).mp hv
  exact Cech.TensorCoefficientChange.coefficientCechModel_quasiIsoAt_of_coefficient_equiv (C := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    (hψ := hw)
    a f.appTop.hom M (specPullbackCoefficientMap (b := b)) b.appTop.hom
    (specPullbackCoefficient_compatible H) (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) U
    (specBaseCoefficientEquiv g) rfl φ n

theorem spec_affineFrame_coefficientCechModel_quasiIsoAt
    [IsAffine S] [X.IsSeparated] [Finite ι]
    (L : Line.Bundles.LineBundle X)
    (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (n : ℕ)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ) n] :
    letI : Algebra Γ(S, ⊤) B := (specBaseCoefficientMap g).toAlgebra
    QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f.appTop.hom L.sheaf (specPullbackCoefficientMap (b := b))
        (specPullbackCoefficient_compatible H) U) n := by
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) :=
    Framed.AffineCechTensorIsomorphism.geometricCechTensorPushforwardMap_isIso H L U ha he
  have : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) n := inferInstance
  exact spec_coefficientCechModel_quasiIsoAt H L.sheaf U φ n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientCechComparison
