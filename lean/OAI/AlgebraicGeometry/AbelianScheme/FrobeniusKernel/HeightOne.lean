import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOneTorsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Diagonalizable

/-! # Height One -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOne.Construction

noncomputable section

/-!
Translate triviality of relative Frobenius into the height-one equation
in a finite Hopf coordinate algebra. This yields the scheme-theoretic
p-torsion bound, with no use of geometric-point detection.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

omit [Module.Finite k A] in
theorem affineGroup_one_left :
    (1 : (Spec (.of A)).asOver (Spec (.of k)) ⟶ (Spec (.of A)).asOver (Spec (.of k))).left =
      Spec.map (CommRingCat.ofHom ((algebraMap k A).comp (Bialgebra.counitAlgHom k A).toRingHom)) := by
  rw [Hom.one_def, Over.comp_left, one_spec_asOver_spec_left]
  change Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ _ = _
  erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

omit [PerfectRing k p] [Module.Finite k A] in
theorem hopfHeightOne_of_trivial_frobenius
    (hF : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
        ((Spec (.of A)).asOver (Spec (.of k))) = 1) : HeightOneTorsion.Construction.HopfHeightOne p k A := by
  let G := (Spec (.of A)).asOver (Spec (.of k))
  let hp : p.Prime := Fact.out
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS G
  have hF' : F = (1 : G ⟶ G) ≫ F := hF.trans (MonObj.one_comp F).symm
  let π : (Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS G).left ⟶ G.left :=
    CategoryTheory.Limits.pullback.fst G.hom (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp _ hS)
  have hπ : F.left ≫ π =
      Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp G.left (Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p hS G.hom) :=
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius_comp_fst p hp hS G
  have hh := hπ.symm.trans
    ((congrArg (fun f : G ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS G => f.left ≫ π) hF').trans
      ((Category.assoc (1 : G ⟶ G).left F.left π).trans
        (congrArg (fun f => (1 : G ⟶ G).left ≫ f) hπ)))
  have hA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero k p, map_zero]
  change Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp (Spec (.of A)) _ =
    (1 : (Spec (.of A)).asOver (Spec (.of k)) ⟶
      (Spec (.of A)).asOver (Spec (.of k))).left ≫
        Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp (Spec (.of A)) _ at hh
  erw [affineGroup_one_left k A, Picard.Homomorphisms.Affine.Construction.absoluteFrobenius_spec p hp A hA, ← Spec.map_comp] at hh
  have hr := Spec.map_injective hh
  intro a
  have ha := congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of A => f.hom a) hr
  change a ^ p = algebraMap k A (Coalgebra.counit (R := k) (a ^ p)) at ha
  exact ha.trans (congrArg (algebraMap k A) (Bialgebra.counit_pow a p))

/-- A finite affine group with trivial relative Frobenius is killed by p
as an actual scheme endomorphism. -/
theorem affineGroup_killed_of_trivial_frobenius
    (hF : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
        ((Spec (.of A)).asOver (Spec (.of k))) = 1) :
    (𝟙 ((Spec (.of A)).asOver (Spec (.of k))) :
      (Spec (.of A)).asOver (Spec (.of k)) ⟶ (Spec (.of A)).asOver (Spec (.of k))) ^ p = 1 :=
  HeightOneTorsion.Construction.heightOne_scheme_power p k A (hopfHeightOne_of_trivial_frobenius p k A hF)

omit [PerfectRing k p] [Module.Finite k A] in
/-- The height-one coordinate equation also implies triviality of the
actual relative Frobenius morphism. -/
theorem trivial_frobenius_of_hopfHeightOne (h : HeightOneTorsion.Construction.HopfHeightOne p k A) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
        ((Spec (.of A)).asOver (Spec (.of k))) = 1 := by
  apply Picard.Homomorphisms.Diagonalizable.Construction.relativeFrobenius_eq_one_of_absolute
  have hA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero k p, map_zero]
  erw [affineGroup_one_left k A,
    Picard.Homomorphisms.Affine.Construction.absoluteFrobenius_spec p (Fact.out : p.Prime) A hA, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change a ^ p = algebraMap k A (Coalgebra.counit (R := k) (a ^ p))
  exact (h a).trans (congrArg (algebraMap k A) (Bialgebra.counit_pow a p).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOne.Construction
