import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplement
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Isogeny Complement Geometry -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplementGeometry

noncomputable section

/-! Geometric properties of the constructed complementary isogeny.
Positive multiplication is finite étale and surjective over a characteristic
zero field. Both multiplication identities therefore make the reverse map
finite étale and surjective as an actual scheme morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {k : Type u} [Field k] [CharZero k]

theorem integer_unit_at_field_stalk (n : ℕ) (hn : 0 < n) (x : Spec (.of k)) :
    IsUnit (n : (Spec (.of k)).presheaf.stalk x) := by
  let constants : k →+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom
  let toStalk : k →+* (Spec (.of k)).presheaf.stalk x :=
    ((Spec (.of k)).presheaf.germ ⊤ x (by trivial)).hom.comp constants
  have hu : IsUnit (n : k) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  simpa only [map_natCast] using hu.map toStalk

variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem positive_multiplication_finite_etale_surjective (n : ℕ) (hn : 0 < n) :
    IsFinite (((𝟙 A : A ⟶ A) ^ n).left) ∧
      Etale (((𝟙 A : A ⟶ A) ^ n).left) ∧ Surjective (((𝟙 A : A ⟶ A) ^ n).left) := by
  let p : A ⟶ A := (𝟙 A : A ⟶ A) ^ n
  have he : Etale p.left := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale A n
    (integer_unit_at_field_stalk n hn)
  have hp : IsProper p.left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.power_isProper A n
  have hf : IsFinite p.left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified p.left
  have : Nonempty (Spec (.of k)) := ⟨IsLocalRing.closedPoint k⟩
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  have hcl : IsClopen (Set.range p.left) := ⟨by
    simpa only [Set.image_univ] using p.left.isClosedMap Set.univ isClosed_univ,
    p.left.isOpenMap.isOpen_range⟩
  have hr : Set.range p.left = Set.univ := hcl.eq_univ (Set.range_nonempty _)
  exact ⟨hf, he, ⟨Set.range_eq_univ.mp hr⟩⟩

variable [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [IsCommMonObj A] [IsCommMonObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]

/-- Both the reverse morphism and its finite étale geometry are
constructed, together with a positive torsion bound for its kernel. -/
theorem exists_complementary_finite_etale_isogeny
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    ∃ (n : ℕ) (d : B ⟶ A), 0 < n ∧ IsMonHom d ∧ IsFinite d.left ∧ Etale d.left ∧
      Surjective d.left ∧ f ≫ d = (𝟙 A : A ⟶ A) ^ n ∧
      d ≫ f = (𝟙 B : B ⟶ B) ^ n ∧
      ∀ (T : Over (Spec (.of k))) (x : T ⟶ B), x ≫ d = 1 → x ^ n = 1 := by
  obtain ⟨n, d, hn, hd, hfd, hdf, hker⟩ := IsogenyComplement.exists_complementary_map_of_finite_etale f
  obtain ⟨_, _, hsurjA⟩ := positive_multiplication_finite_etale_surjective A n hn
  obtain ⟨hfiniteB, hetaleB, _⟩ := positive_multiplication_finite_etale_surjective B n hn
  have hdf' : d.left ≫ f.left = ((𝟙 B : B ⟶ B) ^ n).left := congrArg Over.Hom.left hdf
  have hfd' : f.left ≫ d.left = ((𝟙 A : A ⟶ A) ^ n).left := congrArg Over.Hom.left hfd
  have : IsFinite (d.left ≫ f.left) := hdf' ▸ hfiniteB
  have : Etale (d.left ≫ f.left) := hdf' ▸ hetaleB
  have hdFinite : IsFinite d.left := IsFinite.of_comp d.left f.left
  have hdEtale : Etale d.left := Etale.of_comp d.left f.left
  have : Surjective (f.left ≫ d.left) := hfd' ▸ hsurjA
  have hdSurj : Surjective d.left := by
    constructor
    intro a
    obtain ⟨x, hx⟩ := this.1 a
    exact ⟨f.left x, hx⟩
  exact ⟨n, d, hn, hd, hdFinite, hdEtale, hdSurj, hfd, hdf, hker⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplementGeometry
