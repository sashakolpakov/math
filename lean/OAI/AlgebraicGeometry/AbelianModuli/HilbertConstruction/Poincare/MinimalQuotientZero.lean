import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.QuotientResidueSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorSurjectivityIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.ResidueSectionTensorCriterion

/-! # Minimal Quotient Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The coefficient quotient of a local minimal model of the actual Poincare family maps to the dual zero section when its spectrum is supported at a residue point that is zero. The section comparison is supplied by the universal Cech model and transported through the actual pullback-composition isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S T P : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) [IsAffine T] [IsLocalRing Γ(T, ⊤)] [P.IsSeparated]
variable (t : T ⟶ D.abelian.scheme.left)
variable {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)
variable {ιCover : Type u} [LinearOrder ιCover] [Finite ιCover] (U : ιCover → P.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
  (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
variable {C : CochainComplex (ModuleCat.{u} Γ(T, ⊤)) ℕ}
variable (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
variable (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(T, ⊤) B],
  QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))
variable (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareBaseFamily_minimal_quotient_zero_of_single_point
    (hQ : Subsingleton (Spec (.of (Γ(T, ⊤) ⧸ Q.firstDifferentialIdeal)))) :
    let V := Spec (.of (Γ(T, ⊤) ⧸ Q.firstDifferentialIdeal))
    let j := Affine.QuotientCoefficientMap.affineCoordinateMap (S := T) (Ideal.Quotient.mk Q.firstDifferentialIdeal)
    ∀ x : V,
      V.fromSpecResidueField x ≫ (j ≫ t) =
        ((V.fromSpecResidueField x ≫ (j ≫ t)) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left →
      j ≫ t = ((j ≫ t) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left := by
  let V := Spec (.of (Γ(T, ⊤) ⧸ Q.firstDifferentialIdeal))
  let j : V ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (Ideal.Quotient.mk Q.firstDifferentialIdeal)
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  have : Subsingleton V := hQ
  dsimp only
  intro x hx
  let H' : IsPullback (a' ≫ a) b'
      (pullback.fst D.abelian.scheme.hom A.scheme.hom) (j ≫ t) :=
    (IsPullback.of_hasPullback b j).paste_horiz H
  have hs : Function.Surjective
      ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison (IsPullback.of_hasPullback b' (V.fromSpecResidueField x))
        ((D.poincare.pullback a).pullback a').sheaf).app (op ⊤)) :=
    Minimal.QuotientResidueSections.minimal_quotient_residue_sectionTensor_surjective b (D.poincare.pullback a) U hU ha he φ ht Q x
  let e : ((D.poincare.pullback a).pullback a').sheaf ≅ (D.poincare.pullback (a' ≫ a)).sheaf :=
    (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf
  exact D.poincareBaseFamily_zero_of_residue_section_tensor (j ≫ t) H' x hx
    (Section.TensorSurjectivityIso.baseChangeModuleTensorComparison_surjective_of_iso
      (IsPullback.of_hasPullback b' (V.fromSpecResidueField x)) e ⊤ hs)

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareBaseFamily_minimal_quotient_zero_of_residue_support
    [Nontrivial Q.complex.X₁] (p₀ : PrimeSpectrum Γ(T, ⊤))
    (hsupport : ∀ p : PrimeSpectrum Γ(T, ⊤), p ≠ p₀ →
      Subsingleton (LinearMap.ker
        (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex Γ(T, ⊤) p.asIdeal.ResidueField
          (C.sc' 0 1 2)).f.hom)) :
    let V := Spec (.of (Γ(T, ⊤) ⧸ Q.firstDifferentialIdeal))
    let j := Affine.QuotientCoefficientMap.affineCoordinateMap (S := T) (Ideal.Quotient.mk Q.firstDifferentialIdeal)
    ∀ x : V,
      V.fromSpecResidueField x ≫ (j ≫ t) =
        ((V.fromSpecResidueField x ≫ (j ≫ t)) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left →
      j ≫ t = ((j ≫ t) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left :=
  D.poincareBaseFamily_minimal_quotient_zero_of_single_point t H U hU ha he φ ht Q
    (Q.firstDifferential_quotient_subsingleton p₀ hsupport)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
