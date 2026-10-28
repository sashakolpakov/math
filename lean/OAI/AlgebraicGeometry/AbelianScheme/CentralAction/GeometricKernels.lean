import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateLattices

/-! # Geometric Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricKernels.Construction

noncomputable section

/-! The intrinsic TateComparison Tate preimages determine actual geometric
q-power torsion kernels. This uses the proved divisibility of abelian points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {X Y : Over S} [GrpObj X] [GrpObj Y]
  [IsCommMonObj X] [IsCommMonObj Y]

def schemePointAddHom (T : Over S) (f : X ⟶ Y) [IsMonHom f] :
    Additive (T ⟶ X) →+ Additive (T ⟶ Y) := (IsMonHom.monoidHom f T).toAdditive

theorem schemeTatePreimage_eq_pointPreimage (T : Over S) (q : ℕ) [Fact q.Prime]
    (f : X ⟶ Y) [IsMonHom f] :
    TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) f = TateKernels.Construction.tateAddPreimage q (schemePointAddHom T f) := rfl

variable {K : Type} [Field K] [CharZero K] {g : ℕ}

/-- Equality of intrinsic preimages gives equality of actual kernel
points at every q-power torsion level and every geometric point of the base. -/
theorem geometric_kernel_eq_on_torsion
    (B C D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (base : S ⟶ Spec (.of K))
    (q : ℕ) [Fact q.Prime] {k : Type} [Field k] [IsAlgClosed k]
    (t : Spec (.of k) ⟶ S)
    (f : B.scheme ⟶ C.scheme) [IsMonHom f] (e : B.scheme ⟶ D.scheme) [IsMonHom e]
    (hpre : TateComparison.Rational.isogenyTatePreimage (T := Over.mk t) (q := q) f =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk t) (q := q) e)
    (n : ℕ) (x : Over.mk t ⟶ B.scheme) (hx : x ^ (q ^ n) = 1) :
    x ≫ f = 1 ↔ x ≫ e = 1 := by
  have hx' : q ^ n • Additive.ofMul x = 0 := congrArg Additive.ofMul hx
  rw [schemeTatePreimage_eq_pointPreimage, schemeTatePreimage_eq_pointPreimage] at hpre
  exact TateKernels.Construction.tate_preimage_eq_kernel_on_torsion q
    (TateGeometry.Construction.abelian_geometric_points_divisible B base q (Fact.out : q.Prime).ne_zero t)
    (schemePointAddHom (Over.mk t) f) (schemePointAddHom (Over.mk t) e) hpre n
    (Additive.ofMul x) hx'

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricKernels.Construction
