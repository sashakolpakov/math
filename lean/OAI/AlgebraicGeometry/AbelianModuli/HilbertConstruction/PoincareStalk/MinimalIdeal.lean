import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.MinimalQuotientZero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkQuotientZeroSection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuotientResiduePointZero

/-! # Minimal Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! At the rational dual zero point, the coefficient ideal of a local minimal Poincare model is the maximal ideal once its residue first cycles are supported at one prime and the minimal source is nonzero. The quotient's residue-point zero identity is derived from its actual closed immersion into the stalk spectrum. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)

def Dual.Data.DualAbelianData.poincareZeroStalkScheme : Scheme.{u} :=
  Spec (D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K)))

def Dual.Data.DualAbelianData.poincareZeroStalkParameterMap : D.poincareZeroStalkScheme ⟶ D.abelian.scheme.left :=
  D.abelian.scheme.left.fromSpecStalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))

instance Dual.Data.DualAbelianData.poincareZeroStalkScheme_isAffine : IsAffine D.poincareZeroStalkScheme :=
  inferInstanceAs (IsAffine (Spec (D.abelian.scheme.left.presheaf.stalk
    (η[D.abelian.scheme].left (IsLocalRing.closedPoint K)))))

instance Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isLocalRing : IsLocalRing Γ(D.poincareZeroStalkScheme, ⊤) :=
  Affine.StalkQuotientZeroSection.stalkSpecGlobalSections_isLocalRing D.abelian.scheme.left
    (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))

theorem Dual.Data.DualAbelianData.poincareZeroStalk_firstDifferentialIdeal_eq_maximal_of_residue_support
    {P : Scheme.{u}} [P.IsSeparated]
    {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ D.poincareZeroStalkScheme}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) D.poincareZeroStalkParameterMap)
    {ιCover : Type u} [LinearOrder ιCover] [Finite ιCover] (U : ιCover → P.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
      (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {C : CochainComplex (ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
    (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(D.poincareZeroStalkScheme, ⊤) B],
      QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    [Nontrivial Q.complex.X₁] (p₀ : PrimeSpectrum Γ(D.poincareZeroStalkScheme, ⊤))
    (hsupport : ∀ p : PrimeSpectrum Γ(D.poincareZeroStalkScheme, ⊤), p ≠ p₀ →
      Subsingleton (LinearMap.ker
        (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex Γ(D.poincareZeroStalkScheme, ⊤)
          p.asIdeal.ResidueField (C.sc' 0 1 2)).f.hom)) :
    Q.firstDifferentialIdeal = IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) := by
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  have : IsLocalRing Γ(Spec (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))), ⊤) :=
    Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isLocalRing D
  let I : Ideal R := Q.firstDifferentialIdeal
  let B := R ⧸ I
  let T := Spec (.of B)
  let j : T ⟶ D.poincareZeroStalkScheme := Affine.QuotientCoefficientMap.affineCoordinateMap (Ideal.Quotient.mk I)
  have hI : I ≤ IsLocalRing.maximalIdeal R := Q.firstDifferentialIdeal_le_maximalIdeal
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hT : Subsingleton T := Q.firstDifferential_quotient_subsingleton p₀ hsupport
  have : Subsingleton T := hT
  let x : T := IsLocalRing.closedPoint B
  have hz : η[D.abelian.scheme].left ≫ D.abelian.scheme.hom = 𝟙 (Spec (.of K)) := η[D.abelian.scheme].w
  have hpoint : T.fromSpecResidueField x ≫ (j ≫ D.poincareZeroStalkParameterMap) =
      ((T.fromSpecResidueField x ≫ (j ≫ D.poincareZeroStalkParameterMap)) ≫
        D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left :=
    QuotientResiduePointZero.affine_stalk_quotient_residue_point_zero D.abelian.scheme.hom η[D.abelian.scheme].left hz I x
  have hzero : j ≫ D.poincareZeroStalkParameterMap =
      ((j ≫ D.poincareZeroStalkParameterMap) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left :=
    D.poincareBaseFamily_minimal_quotient_zero_of_single_point D.poincareZeroStalkParameterMap
      H U hU ha he φ ht Q hT x hpoint
  exact Affine.StalkQuotientZeroSection.affine_stalk_quotient_eq_maximal_of_rational_zero
    D.abelian.scheme.hom η[D.abelian.scheme].left hz I hI hzero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
