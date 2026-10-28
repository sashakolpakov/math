import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateKernelLattice
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny

/-! # Tate Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateKernel.Construction

noncomputable section

/-!
Apply the Tate lattice/kernel comparison to actual HilbertConstruction abelian-scheme
isogenies on geometric points. Point divisibility follows from the full
TorsionQuotient input; point surjectivity and finite kernels follow from the isogeny.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem geometricPoint_q_divisible_from_TorsionQuotient
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (.of K)) {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
    {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
    (q : ℕ) (hq : q.Prime) (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u})
    (x : Additive (Over.mk b ⟶ A.scheme)) : ∃ y, q • y = x := by
  obtain ⟨hfinite, _, hsurj, _, _⟩ := Multiplication.Construction.multiplication_geometry_from_TorsionQuotient A.scheme q
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient base q hq.pos h_TorsionQuotient)
  let : IsFinite (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ q).left) := hfinite
  let : Surjective (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ q).left) := hsurj
  obtain ⟨y, hy⟩ := Points.Construction.surjective_on_geometric_points ((𝟙 A.scheme) ^ q) k b x.toMul
  refine ⟨Additive.ofMul y, ?_⟩
  apply Additive.toMul.injective
  change y ^ q = x.toMul
  simpa only [MonObj.comp_pow, Category.comp_id] using hy

def isogenyKernelAdditiveEquiv
    {S : Scheme.{u}} {d e : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme e S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (T : Over S) :
    (A.mapPoints B f.hom T).toAdditive.ker ≃+ Additive (f.kernelAt T) where
  toFun x := Additive.ofMul ⟨x.val.toMul, x.property⟩
  invFun x := ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- For the actual scheme isogeny and its constructed complementary map,
the rational Tate preimage quotient is its actual geometric kernel. -/
def geometricIsogenyLatticeKernelEquiv
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (.of K)) {d e : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme e S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : B.scheme ⟶ A.scheme) [IsMonHom g]
    (q h : ℕ) [Fact q.Prime]
    (hfg : f.hom ≫ g = (𝟙 A.scheme) ^ (q ^ h))
    (hgf : g ≫ f.hom = (𝟙 B.scheme) ^ (q ^ h))
    {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S) (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u}) :
    TateComparison.Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom ⧸
      ((TateComparison.Rational.integralTateImage A.scheme (Over.mk b) q).comap
        (TateComparison.Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom).subtype).toAddSubgroup ≃+
      Additive (f.kernelAt (Over.mk b)) := by
  let φ := (A.mapPoints B f.hom (Over.mk b)).toAdditive
  let ψ := (B.mapPoints A g (Over.mk b)).toAdditive
  have hφψ (y : Additive (Over.mk b ⟶ B.scheme)) : φ (ψ y) = (q ^ h) • y := by
    apply Additive.toMul.injective
    change (y.toMul ≫ g) ≫ f.hom = y.toMul ^ (q ^ h)
    rw [Category.assoc, hgf, MonObj.comp_pow, Category.comp_id]
  have hψφ (x : Additive (Over.mk b ⟶ A.scheme)) : ψ (φ x) = (q ^ h) • x := by
    apply Additive.toMul.injective
    change (x.toMul ≫ f.hom) ≫ g = x.toMul ^ (q ^ h)
    rw [Category.assoc, hfg, MonObj.comp_pow, Category.comp_id]
  have hφ : Function.Surjective φ := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective f b
  let : Finite (f.kernelAt (Over.mk b)) := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite f b
  let : Finite φ.ker := Finite.of_equiv (Additive (f.kernelAt (Over.mk b)))
    (isogenyKernelAdditiveEquiv f (Over.mk b)).symm.toEquiv
  exact (TateKernelLattice.Construction.tateTargetPreimageQuotientEquiv q h φ ψ hφψ hψφ hφ
    (geometricPoint_q_divisible_from_TorsionQuotient base A b q Fact.out h_TorsionQuotient)).trans
      (isogenyKernelAdditiveEquiv f (Over.mk b))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateKernel.Construction
