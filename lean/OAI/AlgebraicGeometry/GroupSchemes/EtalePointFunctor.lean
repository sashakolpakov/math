import OAI.AlgebraicGeometry.GroupSchemes.ConstantPoints
import OAI.AlgebraicGeometry.GroupSchemes.PointSpecialization
import OAI.AlgebraicGeometry.GroupSchemes.SplitAlgebra

/-! # Etale Point Functor -/

namespace OAI.AlgebraicGeometry.GroupSchemes.EtalePointFunctor.Finite.FiniteCommGroupScheme

noncomputable section

/-! The full point functor of a split finite group scheme is its locally constant point functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.GroupSchemes.ConstantPoints.FiniteEtale

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

local instance (G : FiniteEtale.FiniteCommGroupScheme k) : Fintype G.rationalPoints := Fintype.ofFinite _

/-- Evaluation at all rational points is the canonical split coordinate algebra. -/
def _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etaleCoordinateEquiv (G : FiniteEtale.FiniteCommGroupScheme k) [Algebra.IsFiniteSplit k G.algebra] :
    G.algebra ≃ₐ[k] (G.rationalPoints → k) :=
  SplitAlgebra.FiniteEtale.evaluationEquiv k G.algebra G.rationalPointsEquivAlgHom
    G.rationalPointsEquivAlgHom.injective
    (by simpa only [Nat.card_eq_fintype_card] using G.rationalPoints_card)

theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etaleCoordinateEquiv_apply (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.algebra] (a : G.algebra) (x : G.rationalPoints) :
    G.etaleCoordinateEquiv a x = G.rationalPointsEquivAlgHom x a := rfl

/-- All affine points of the split group, as locally constant rational-point functions. -/
def _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv (G : FiniteEtale.FiniteCommGroupScheme k) [Algebra.IsFiniteSplit k G.algebra]
    (R : CommAlgCat.{u} k) :
    (FiniteEtale.affine k R ⟶ G.scheme) ≃ LocallyConstant (PrimeSpectrum R) G.rationalPoints :=
  ((G.coordinatePoints R).toEquiv.symm.trans (WithConv.equiv _)).trans
    ((G.etaleCoordinateEquiv.arrowCongr (AlgEquiv.refl : R ≃ₐ[k] R)).trans (ConstantPoints.FiniteEtale.constantPointsEquiv k))

theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_coordinate (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.algebra] (R : CommAlgCat.{u} k) (f : G.algebra →ₐ[k] R) :
    G.etalePointsEquiv R (G.coordinatePoints R (toConv f)) =
      ConstantPoints.FiniteEtale.constantPointsEquiv k (f.comp G.etaleCoordinateEquiv.symm.toAlgHom) := by
  change ConstantPoints.FiniteEtale.constantPointsEquiv k
    ((G.etaleCoordinateEquiv.arrowCongr (AlgEquiv.refl : R ≃ₐ[k] R))
      (((G.coordinatePoints R).symm (G.coordinatePoints R (toConv f))).ofConv)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The locally constant description is the group-valued specialization at each prime. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_coordinate_prime (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.algebra] (R : CommAlgCat.{u} k) (P : PrimeSpectrum R)
    (f : G.algebra →ₐ[k] R) :
    G.etalePointsEquiv R (G.coordinatePoints R (toConv f)) P =
      G.pointAtPrime R P (G.coordinatePoints R (toConv f)) := by
  classical
  rw [FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_coordinate]
  let y := G.pointAtPrime R P (G.coordinatePoints R (toConv f))
  apply (ConstantPoints.FiniteEtale.constantPointsEquiv_eq_iff k (f.comp G.etaleCoordinateEquiv.symm.toAlgHom) P y).mpr
  let t := G.etaleCoordinateEquiv.symm (Pi.single y (1 : k))
  have ht : G.rationalPointsEquivAlgHom y t = 1 := by
    have h := congrFun (G.etaleCoordinateEquiv.apply_symm_apply (Pi.single y (1 : k))) y
    change G.rationalPointsEquivAlgHom y t = (Pi.single y (1 : k) : G.rationalPoints → k) y at h
    simpa only [Pi.single_eq_same] using h
  have he := AlgHom.congr_fun (G.pointAtPrime_coordinates R P f) t
  have hmod : Ideal.Quotient.mk P.asIdeal (f t) = 1 := by
    change Ideal.Quotient.mk P.asIdeal (f t) = algebraMap k (R ⧸ P.asIdeal)
      (G.rationalPointsEquivAlgHom y t) at he
    simpa only [ht, map_one] using he
  intro hm
  change f t ∈ P.asIdeal at hm
  exact zero_ne_one ((Ideal.Quotient.eq_zero_iff_mem.mpr hm).symm.trans hmod)

theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_prime (G : FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.algebra] (R : CommAlgCat.{u} k) (P : PrimeSpectrum R)
    (x : FiniteEtale.affine k R ⟶ G.scheme) : G.etalePointsEquiv R x P = G.pointAtPrime R P x := by
  let f : G.algebra →ₐ[k] R := ((G.coordinatePoints R).symm x).ofConv
  have hf : G.coordinatePoints R (toConv f) = x := (G.coordinatePoints R).apply_symm_apply x
  rw [← hf]
  exact G.etalePointsEquiv_coordinate_prime R P f

/-- The all-affine locally constant description preserves the original geometric group law. -/
def _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etalePointsMulEquiv (G : FiniteEtale.FiniteCommGroupScheme k) [Algebra.IsFiniteSplit k G.algebra]
    (R : CommAlgCat.{u} k) :
    (FiniteEtale.affine k R ⟶ G.scheme) ≃* LocallyConstant (PrimeSpectrum R) G.rationalPoints where
  __ := G.etalePointsEquiv R
  map_mul' x y := by
    apply LocallyConstant.ext
    intro P
    change G.etalePointsEquiv R (x * y) P =
      G.etalePointsEquiv R x P * G.etalePointsEquiv R y P
    rw [FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_prime, FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_prime, FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_prime]
    exact (G.pointAtPrime R P).map_mul x y

/-- The all-affine group equivalence is natural in the test algebra. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etalePoints_naturality (G : FiniteEtale.FiniteCommGroupScheme k) [Algebra.IsFiniteSplit k G.algebra]
    {R S : CommAlgCat.{u} k} (a : R ⟶ S) (x : FiniteEtale.affine k R ⟶ G.scheme) :
    G.etalePointsMulEquiv S ((G.points.map a) x) =
      (G.etalePointsMulEquiv R x).comap
        ⟨PrimeSpectrum.comap a.hom.toRingHom, PrimeSpectrum.continuous_comap _⟩ := by
  let f : G.algebra →ₐ[k] R := ((G.coordinatePoints R).symm x).ofConv
  have hf : G.coordinatePoints R (toConv f) = x := (G.coordinatePoints R).apply_symm_apply x
  rw [← hf]
  change G.etalePointsEquiv S ((algSpec (CommRingCat.of k)).map a.op ≫
    G.coordinatePoints R (toConv f)) = (G.etalePointsEquiv R (G.coordinatePoints R (toConv f))).comap _
  rw [← G.coordinatePoints_precomp a f]
  exact (G.etalePointsEquiv_coordinate S (a.hom.comp f)).trans
    ((ConstantPoints.FiniteEtale.constantPointsEquiv_naturality k a.hom (f.comp G.etaleCoordinateEquiv.symm.toAlgHom)).trans
      (congrArg (fun z : LocallyConstant (PrimeSpectrum R) G.rationalPoints => z.comap
        ⟨PrimeSpectrum.comap a.hom.toRingHom, PrimeSpectrum.continuous_comap _⟩)
        (G.etalePointsEquiv_coordinate R f).symm))

/-- The locally constant point description also respects geometric morphisms. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.etalePoints_postcomp {G H : FiniteEtale.FiniteCommGroupScheme k}
    [Algebra.IsFiniteSplit k G.algebra] [Algebra.IsFiniteSplit k H.algebra]
    (h : G.scheme ⟶ H.scheme) (R : CommAlgCat.{u} k) (x : FiniteEtale.affine k R ⟶ G.scheme) :
    H.etalePointsMulEquiv R (x ≫ h) =
      (G.etalePointsMulEquiv R x).map (fun y => y ≫ h) := by
  apply LocallyConstant.ext
  intro P
  change H.etalePointsEquiv R (x ≫ h) P = G.etalePointsEquiv R x P ≫ h
  rw [FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_prime, FiniteEtale.FiniteCommGroupScheme.etalePointsEquiv_prime]
  exact FiniteEtale.FiniteCommGroupScheme.pointAtPrime_postcomp h R P x

end

end OAI.AlgebraicGeometry.GroupSchemes.EtalePointFunctor.Finite.FiniteCommGroupScheme
