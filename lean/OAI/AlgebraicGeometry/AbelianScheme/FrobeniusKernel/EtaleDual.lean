import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleDualHeightOne
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Scalar
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced

/-! # Etale Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
The constructed Cartier group of an etale p-torsion group has trivial
relative Frobenius. The assertion concerns its actual character group
law, not an assumed comparison with a coordinate Hopf group law.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv
open scoped _root_.CategoryTheory.MonObj

universe u

section Coordinates

variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]
variable [Coalgebra.IsCocomm k A]

theorem EtaleDual.Construction.convolution_power_of_scheme_power (n : ℕ)
    (h : (𝟙 ((Spec (.of A)).asOver (Spec (.of k))) :
      (Spec (.of A)).asOver (Spec (.of k)) ⟶ (Spec (.of A)).asOver (Spec (.of k))) ^ n = 1)
    (a : A) : ((toConv (LinearMap.id : A →ₗ[k] A)) ^ n) a =
      algebraMap k A (Coalgebra.counit (R := k) a) := by
  let e := Spec.mapMulEquiv (R := k) (S := A) (T := A)
  have he : e (toConv (AlgHom.id k A)) = 𝟙 ((Spec (.of A)).asOver (Spec (.of k))) := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  have hp : (toConv (AlgHom.id k A) : WithConv (A →ₐ[k] A)) ^ n = 1 := by
    apply e.injective
    exact (map_pow e _ n).trans
      ((congrArg (fun f => f ^ n) he).trans (h.trans e.map_one.symm))
  exact (congrArg (fun f : WithConv (A →ₗ[k] A) => f a)
    (AlgHom.toLinearMap_convPow (toConv (AlgHom.id k A)) n)).symm.trans
      (congrArg (fun f : WithConv (A →ₐ[k] A) => f.ofConv a) hp)

end Coordinates

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable {G : Grp (Over (Spec (.of k)))} (P : CartierModel.Construction.CartierCoordinates (.of k) G)

/-- Reduced p-torsion dualizes to a height-one group scheme on every
test scheme, using the actual represented character multiplication. -/
theorem CartierModel.Construction.CartierCoordinates.dual_frobenius_of_reduced_torsion
    [AlgebraicGeometry.IsReduced G.X.left] (hG : (𝟙 G.X) ^ p = 1) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) P.dualGroup.X = 1 := by
  have : Coalgebra.IsCocomm k P.algebra := P.cocommutative
  have : Module.Finite k P.algebra := P.finite
  let f : Spec (.of P.algebra) ⟶ G.X.left := P.comparison.hom.hom.hom.left
  have : IsIso f := inferInstanceAs
    (IsIso (((Grp.forget (Over (Spec (.of k)))) ⋙ Over.forget _).map P.comparison.hom))
  have : AlgebraicGeometry.IsReduced (Spec (.of P.algebra)) :=
    isReduced_of_isOpenImmersion f
  have : _root_.IsReduced P.algebra := (affine_isReduced_iff (.of P.algebra)).mp inferInstance
  have hP := FiniteTorsion.Construction.group_power_of_iso P.comparison.symm p hG
  have hd := EtaleDualHeightOne.Construction.dual_heightOne_of_reduced_torsion p k P.algebra
    (EtaleDual.Construction.convolution_power_of_scheme_power k P.algebra p hP)
  have : IsCommMonObj P.dualGroup.X := P.dualGroup_commutative
  have : IsFinite P.dualGroup.X.hom := P.dualGroup_finite
  have : Flat P.dualGroup.X.hom := P.dualGroup_flat
  have : LocallyOfFinitePresentation P.dualGroup.X.hom := P.dualGroup_finitelyPresented
  apply Scalar.Construction.finiteGroup_frobenius_of_scalar_powers p k P.dualGroup
    (CartierDuality.DualAlgebra.Construction.DualCoordinate k P.algebra) (Iso.refl _)
  intro b
  exact ⟨(Coalgebra.counit (R := k) b) ^ p, hd b⟩

/-- In particular this applies to each ordinary etale torsion factor. -/
theorem CartierModel.Construction.CartierCoordinates.dual_frobenius_of_etale_torsion
    [Etale G.X.hom] (hG : (𝟙 G.X) ^ p = 1) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) P.dualGroup.X = 1 := by
  have : AlgebraicGeometry.IsReduced G.X.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field G.X.hom
  exact P.dual_frobenius_of_reduced_torsion p k hG

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
