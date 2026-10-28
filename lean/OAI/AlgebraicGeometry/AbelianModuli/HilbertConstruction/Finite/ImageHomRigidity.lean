import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedConnectedImages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismScalarMorphisms

/-! # Image Hom Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An abelian-variety homomorphism with finite underlying image is zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))

theorem Finite.ImageHomRigidity.abelianHom_eq_one_of_finite_range (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (hfinite : (Set.range f.left).Finite) : f = 1 := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : ConnectedSpace A.scheme.left := A.connected_overField
  have : JacobsonSpace B.scheme.left := LocallyOfFiniteType.jacobsonSpace B.scheme.hom
  have : IsProper (f.left ≫ B.scheme.hom) := f.w.symm ▸ inferInstanceAs (IsProper A.scheme.hom)
  have : IsProper f.left := IsProper.of_comp f.left B.scheme.hom
  have hr := HilbertConstruction.Finite.ClosedConnectedImages.finite_closed_connected_range_subsingleton f.left f.left.continuous
    f.left.isClosedMap.isClosed_range hfinite
  let z : A.scheme.left := η[A.scheme].left (IsLocalRing.closedPoint K)
  let U := B.scheme.left.affineCover.X (B.scheme.left.affineCover.idx (f.left z))
  let j := B.scheme.left.affineCover.f (B.scheme.left.affineCover.idx (f.left z))
  have hj : f.left z ∈ Set.range j := B.scheme.left.affineCover.covers (f.left z)
  have hR : Set.range f.left ⊆ Set.range j := by
    intro y hy
    exact (hr hy ⟨z, rfl⟩).symm ▸ hj
  let q := IsOpenImmersion.lift j f.left hR
  have he := Proper.ConnectedReducedConstants.properConnectedReduced_map_eq_constant A.scheme.hom q η[A.scheme].left η[A.scheme].w
  have hq : q ≫ j = f.left := IsOpenImmersion.lift_fac _ _ _
  have hf' : f.left = A.scheme.hom ≫ η[A.scheme].left ≫ f.left := by
    have h := congrArg (fun b => b ≫ j) he
    simpa only [Category.assoc, hq] using h
  have hz : η[A.scheme].left ≫ f.left = η[B.scheme].left :=
    congrArg Over.Hom.left (IsMonHom.one_hom f)
  apply Over.OverMorphism.ext
  exact hf'.trans (congrArg (fun u => A.scheme.hom ≫ u) hz)

theorem Abelian.Schemes.AbelianScheme.endRing_eq_zero_of_finite_range (d : A.EndRing)
    (hfinite : (Set.range d.toMul.hom.hom.left).Finite) : d = 0 := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact HilbertConstruction.Finite.ImageHomRigidity.abelianHom_eq_one_of_finite_range A A d.toMul.hom.hom hfinite

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
