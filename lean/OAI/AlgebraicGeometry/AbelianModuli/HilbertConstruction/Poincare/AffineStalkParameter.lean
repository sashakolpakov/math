import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.StalkLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.ZeroAffineLift

/-! # Affine Stalk Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical dual-zero stalk is a localization of every affine open neighborhood of zero, with an actual parameter map to that open commuting with the Poincare parameter maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance Poincare.AffineStalkParameter.stalkPoint_isPrime {T : Scheme.{u}} [IsAffine T] (x : T) :
    (T.isoSpec.hom x).asIdeal.IsPrime :=
  (show PrimeSpectrum Γ(T, ⊤) from T.isoSpec.hom x).isPrime

@[instance_reducible]
def Poincare.AffineStalkParameter.affineOpenTargetStalkAlgebraOfEq
    {T X : Scheme.{u}} [IsAffine T] (t : T ⟶ X) [IsOpenImmersion t]
    (x : T) {y : X} (h : t x = y) : Algebra Γ(T, ⊤) (X.presheaf.stalk y) :=
  h ▸ AffineOpen.StalkLocalization.affineOpenTargetStalkAlgebra t x

theorem Poincare.AffineStalkParameter.affineOpenTargetStalk_isLocalization_of_eq
    {T X : Scheme.{u}} [IsAffine T] (t : T ⟶ X) [IsOpenImmersion t]
    (x : T) {y : X} (h : t x = y) :
    let : Algebra Γ(T, ⊤) (X.presheaf.stalk y) := Poincare.AffineStalkParameter.affineOpenTargetStalkAlgebraOfEq t x h;
    IsLocalization (T.isoSpec.hom x).asIdeal.primeCompl (X.presheaf.stalk y) := by
  subst y
  exact AffineOpen.StalkLocalization.affineOpenTargetStalk_isLocalization t x

theorem Poincare.AffineStalkParameter.affineOpenTargetStalk_coordinateMap_comp_of_eq
    {T X : Scheme.{u}} [IsAffine T] (t : T ⟶ X) [IsOpenImmersion t]
    (x : T) {y : X} (h : t x = y) :
    let : Algebra Γ(T, ⊤) (X.presheaf.stalk y) := Poincare.AffineStalkParameter.affineOpenTargetStalkAlgebraOfEq t x h;
    Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(T, ⊤) (X.presheaf.stalk y)) ≫ t = X.fromSpecStalk y := by
  subst y
  exact AffineOpen.StalkLocalization.affineOpenTargetStalk_coordinateMap_comp t x

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) {T : Scheme.{u}} [IsAffine T]
variable (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
variable (hx : η[D.abelian.scheme].left (IsLocalRing.closedPoint K) ∈ Set.range t)

omit [IsAffine T] in
theorem Dual.Data.DualAbelianData.poincareAffineZeroLift_point :
    t (D.poincareAffineZeroLift t hx (IsLocalRing.closedPoint K)) =
      η[D.abelian.scheme].left (IsLocalRing.closedPoint K) :=
  congrArg (fun f : Spec (.of K) ⟶ D.abelian.scheme.left => f (IsLocalRing.closedPoint K))
    (D.poincareAffineZeroLift_fac t hx)

@[instance_reducible]
def Dual.Data.DualAbelianData.poincareAffineStalkAlgebra :
    Algebra Γ(T, ⊤) (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))) :=
  Poincare.AffineStalkParameter.affineOpenTargetStalkAlgebraOfEq t
    (D.poincareAffineZeroLift t hx (IsLocalRing.closedPoint K)) (D.poincareAffineZeroLift_point t hx)

theorem Dual.Data.DualAbelianData.poincareAffineStalk_isLocalization :
    letI : (D.poincareAffineParameterIdeal t).IsMaximal :=
      D.poincareAffineParameterIdeal_isMaximal_of_zero_mem t hx;
    let : Algebra Γ(T, ⊤) (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))) := D.poincareAffineStalkAlgebra t hx;
    IsLocalization (D.poincareAffineParameterIdeal t).primeCompl
      (D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))) := by
  let : (D.poincareAffineParameterIdeal t).IsMaximal :=
    D.poincareAffineParameterIdeal_isMaximal_of_zero_mem t hx
  let : Algebra Γ(T, ⊤) (D.abelian.scheme.left.presheaf.stalk
    (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))) := D.poincareAffineStalkAlgebra t hx
  have hi : D.poincareAffineParameterIdeal t =
      (T.isoSpec.hom (D.poincareAffineZeroLift t hx (IsLocalRing.closedPoint K))).asIdeal :=
    D.poincareAffineParameterIdeal_eq_rationalPointIdeal t
      (D.poincareAffineZeroLift t hx) (D.poincareAffineZeroLift_fac t hx)
  have hh : ∀ (J : Ideal Γ(T, ⊤)) [J.IsPrime],
      J = (T.isoSpec.hom (D.poincareAffineZeroLift t hx (IsLocalRing.closedPoint K))).asIdeal →
      IsLocalization J.primeCompl
        (D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))) := by
    intro J _ hJ
    subst J
    exact Poincare.AffineStalkParameter.affineOpenTargetStalk_isLocalization_of_eq t
      (D.poincareAffineZeroLift t hx (IsLocalRing.closedPoint K)) (D.poincareAffineZeroLift_point t hx)
  exact hh _ hi

def Dual.Data.DualAbelianData.poincareAffineStalkParameterMap : D.poincareZeroStalkScheme ⟶ T :=
  letI := D.poincareAffineStalkAlgebra t hx
  Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(T, ⊤)
    (D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))))

theorem Dual.Data.DualAbelianData.poincareAffineStalkParameterMap_fac :
    D.poincareAffineStalkParameterMap t hx ≫ t = D.poincareZeroStalkParameterMap :=
  Poincare.AffineStalkParameter.affineOpenTargetStalk_coordinateMap_comp_of_eq t
    (D.poincareAffineZeroLift t hx (IsLocalRing.closedPoint K)) (D.poincareAffineZeroLift_point t hx)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
