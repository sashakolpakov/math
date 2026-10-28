import OAI.AlgebraicGeometry.GroupSchemes.CoordinateMaps

/-! # Coordinate Points -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Recover all affine-valued points with their original group law in coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj WithConv

namespace CoordinatePoints.FiniteEtale

/-- Postcomposition by an algebra map commutes with convolution powers. -/
theorem comp_convolution_pow {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Algebra k B] (f : A →ₐ[k] B) (n : ℕ) :
    f.comp ((toConv (AlgHom.id k A)) ^ n).ofConv = ((toConv f) ^ n).ofConv := by
  induction n with
  | zero =>
    ext x
    simp only [pow_zero, AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.commutes]
  | succ n ih =>
    rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ih]
    rfl

end CoordinatePoints.FiniteEtale

universe u
variable {k : Type u} [Field k]

/-- The coordinate presentation of the original functor of points, including its group law. -/
def FiniteEtale.FiniteCommGroupScheme.coordinatePoints (G : FiniteEtale.FiniteCommGroupScheme k) (R : CommAlgCat.{u} k) :
    letI := G.coordinateHopf
    letI : Bialgebra k G.algebra := G.coordinateHopf.toBialgebra
    letI : Algebra k G.algebra := G.coordinateHopf.toAlgebra
    WithConv (G.algebra →ₐ[k] R) ≃* (FiniteEtale.affine k R ⟶ G.scheme) := by
  let := G.coordinateHopf
  let : Bialgebra k G.algebra := G.coordinateHopf.toBialgebra
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  let e := @Spec.mapMulEquiv k G.algebra R _ _ _ G.coordinateHopf.toBialgebra _
  refine { e.toEquiv with map_mul' := ?_ }
  intro f g
  have h := congrArg Over.Hom.left (e.map_mul f g)
  ext1
  simp only [Hom.mul_def, Over.comp_left, mul_spec_asOver_spec_left] at h
  change _ = _ ≫ G.givenMultiplication
  rw [← G.coordinateHopf_represents_mul]
  exact h

/-- Evaluation of the coordinate equivalence is the actual Spec map. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinatePoints_apply (G : FiniteEtale.FiniteCommGroupScheme k) (R : CommAlgCat.{u} k)
    (f : G.algebra →ₐ[k] R) :
    G.coordinatePoints R (toConv f) =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op := rfl

/-- Coordinate evaluation intertwines postcomposition with a geometric morphism. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinatePoints_postcomp {G H : FiniteEtale.FiniteCommGroupScheme k}
    (h : G.scheme ⟶ H.scheme) (R : CommAlgCat.{u} k) (f : G.algebra →ₐ[k] R) :
    H.coordinatePoints R (toConv (f.comp (FiniteEtale.FiniteCommGroupScheme.coordinateMap h))) =
      G.coordinatePoints R (toConv f) ≫ h := by
  change (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (f.comp (FiniteEtale.FiniteCommGroupScheme.coordinateMap h))).op =
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ h
  conv_rhs => rw [← FiniteEtale.FiniteCommGroupScheme.coordinateMap_spec h]
  rw [← Functor.map_comp]
  apply congrArg ((algSpec (CommRingCat.of k)).map)
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  rfl

/-- Coordinate evaluation is natural in every affine test algebra. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinatePoints_precomp (G : FiniteEtale.FiniteCommGroupScheme k)
    {R S : CommAlgCat.{u} k} (a : R ⟶ S) (f : G.algebra →ₐ[k] R) :
    G.coordinatePoints S (toConv (a.hom.comp f)) =
      (algSpec (CommRingCat.of k)).map a.op ≫ G.coordinatePoints R (toConv f) := by
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (a.hom.comp f)).op =
    (algSpec (CommRingCat.of k)).map a.op ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op
  rw [← Functor.map_comp]
  apply congrArg ((algSpec (CommRingCat.of k)).map)
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  rfl

/-- Injectivity on geometric points is equivalent to injectivity on their algebra maps. -/
theorem FiniteEtale.FiniteCommGroupScheme.pointMap_injective_iff (G : FiniteEtale.FiniteCommGroupScheme k)
    {R S : CommAlgCat.{u} k} (a : R ⟶ S) :
    Function.Injective (G.points.map a) ↔
      Function.Injective (a.hom.comp : (G.algebra →ₐ[k] R) → G.algebra →ₐ[k] S) := by
  constructor
  · intro h f g hfg
    apply WithConv.toConv_injective
    apply (G.coordinatePoints R).injective
    apply h
    exact (G.coordinatePoints_precomp a f).symm.trans
      ((congrArg (fun b => G.coordinatePoints S (toConv b)) hfg).trans
        (G.coordinatePoints_precomp a g))
  · intro h x y hxy
    let f : G.algebra →ₐ[k] R := ((G.coordinatePoints R).symm x).ofConv
    let g : G.algebra →ₐ[k] R := ((G.coordinatePoints R).symm y).ofConv
    have hf : G.coordinatePoints R (toConv f) = x := (G.coordinatePoints R).apply_symm_apply x
    have hg : G.coordinatePoints R (toConv g) = y := (G.coordinatePoints R).apply_symm_apply y
    have hfg : a.hom.comp f = a.hom.comp g := by
      apply WithConv.toConv_injective
      apply (G.coordinatePoints S).injective
      exact (G.coordinatePoints_precomp a f).trans
        ((congrArg (fun z => (algSpec (CommRingCat.of k)).map a.op ≫ z) hf).trans
          (hxy.trans ((congrArg (fun z => (algSpec (CommRingCat.of k)).map a.op ≫ z) hg).symm.trans
            (G.coordinatePoints_precomp a g).symm)))
    exact hf.symm.trans ((congrArg (fun b => G.coordinatePoints R (toConv b)) (h hfg)).trans hg)

/-- Pullback of multiplication by n, constructed as the n-fold convolution of the identity. -/
def FiniteEtale.FiniteCommGroupScheme.coordinatePower (G : FiniteEtale.FiniteCommGroupScheme k) (n : ℕ) :
    G.algebra →ₐ[k] G.algebra := by
  let := G.coordinateHopf
  let : Bialgebra k G.algebra := G.coordinateHopf.toBialgebra
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  exact ((toConv (AlgHom.id k G.algebra)) ^ n).ofConv

/-- Pullback of the identity section. -/
def FiniteEtale.FiniteCommGroupScheme.coordinateAugmentation (G : FiniteEtale.FiniteCommGroupScheme k) : G.algebra →ₐ[k] k := by
  let := G.coordinateHopf
  exact Bialgebra.counitAlgHom k G.algebra

/-- Pullback of the constant identity point in any affine algebra. -/
def FiniteEtale.FiniteCommGroupScheme.coordinateIdentity (G : FiniteEtale.FiniteCommGroupScheme k) (R : CommAlgCat.{u} k) :
    G.algebra →ₐ[k] R :=
  (Algebra.ofId k R).comp G.coordinateAugmentation

/-- The pointwise n-torsion equation is precisely its coordinate algebra equation. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinatePoints_pow_eq_one_iff (G : FiniteEtale.FiniteCommGroupScheme k)
    (R : CommAlgCat.{u} k) (f : G.algebra →ₐ[k] R) (n : ℕ) :
    (G.coordinatePoints R (toConv f)) ^ n = 1 ↔
      f.comp (G.coordinatePower n) = G.coordinateIdentity R := by
  let := G.coordinateHopf
  let : Bialgebra k G.algebra := G.coordinateHopf.toBialgebra
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  rw [← map_pow, ← (G.coordinatePoints R).map_one, (G.coordinatePoints R).injective.eq_iff]
  change ((toConv f : WithConv (G.algebra →ₐ[k] R)) ^ n) = 1 ↔ _
  rw [← WithConv.ofConv_injective.eq_iff]
  rw [← CoordinatePoints.FiniteEtale.comp_convolution_pow f n]
  rfl

/-- Coordinate multiplication by n agrees with convolution on linear endomorphisms. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinatePower_apply (G : FiniteEtale.FiniteCommGroupScheme k) (n : ℕ) (x : G.algebra) :
    letI := G.coordinateHopf
    letI := G.coordinateCoalgebra
    G.coordinatePower n x = ((toConv (LinearMap.id : G.algebra →ₗ[k] G.algebra)) ^ n) x := by
  let := G.coordinateHopf
  let : Bialgebra k G.algebra := G.coordinateHopf.toBialgebra
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  have h := AlgHom.toLinearMap_convPow (toConv (AlgHom.id k G.algebra)) n
  exact congrArg (fun f : WithConv (G.algebra →ₗ[k] G.algebra) => f x) h

end

end OAI.AlgebraicGeometry.GroupSchemes
