import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.Data.Int.Cast.Lemmas

/-! # Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters.Construction

noncomputable section

/-!
# CartierDuality: characters of affine group schemes

The multiplicative group is the group scheme of the Hopf algebra R[ℤ].
The character correspondence below uses actual Hopf-algebra morphisms and
the proved fully faithful Spec functor, rather than defining characters
to be elements of the constructed Cartier dual.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

section MonoidAlgebra

variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Bialgebra R A]
variable (G : Type w) [Monoid G]

/-- Restriction of a bialgebra homomorphism to the group-like generators. -/
def bialgMapToGroupLike (h : MonoidAlgebra R G →ₐc[R] A) : G →* GroupLike R A where
  toFun g := ⟨h (MonoidAlgebra.of R G g),
    (MonoidAlgebra.isGroupLikeElem_of (R := R) (A := R) g).map h⟩
  map_one' := by
    apply GroupLike.val_injective
    change h (MonoidAlgebra.of R G 1) = 1
    rw [(MonoidAlgebra.of R G).map_one]
    exact h.toAlgHom.map_one
  map_mul' x y := by
    apply GroupLike.val_injective
    change h (MonoidAlgebra.of R G (x * y)) =
      h (MonoidAlgebra.of R G x) * h (MonoidAlgebra.of R G y)
    rw [(MonoidAlgebra.of R G).map_mul]
    exact h.toAlgHom.map_mul _ _

/-- The universal property of the monoid algebra with its bialgebra structure. -/
def monoidAlgebraBialgHomEquiv :
    (MonoidAlgebra R G →ₐc[R] A) ≃ (G →* GroupLike R A) where
  toFun := bialgMapToGroupLike R A G
  invFun h := (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := A)).comp
    (MonoidAlgebra.mapDomainBialgHom R h)
  left_inv h := by
    apply MonoidAlgebra.bialgHom_ext
    · intro g
      simp [MonoidAlgebra.liftGroupLikeBialgHom, bialgMapToGroupLike]
    · exact Subsingleton.elim _ _
  right_inv h := by
    ext g
    simp [bialgMapToGroupLike, MonoidAlgebra.liftGroupLikeBialgHom]

end MonoidAlgebra

section MultiplicativeGroup

variable (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The Laurent group algebra, the coordinate Hopf algebra of G_m. -/
abbrev MultiplicativeGroupCoordinate := MonoidAlgebra R (Multiplicative ℤ)

/-- A character is determined by the image of the Laurent generator. -/
def groupLikeEquivHopfCharacters :
    GroupLike R A ≃ (MultiplicativeGroupCoordinate R →ₐc[R] A) :=
  (zpowersHom (GroupLike R A)).trans
    (monoidAlgebraBialgHomEquiv R A (Multiplicative ℤ)).symm

/-- The Laurent generator is sent to the group-like element defining
the character. -/
@[simp]
theorem groupLikeEquivHopfCharacters_generator (z : GroupLike R A) :
    groupLikeEquivHopfCharacters R A z
      (MonoidAlgebra.of R (Multiplicative ℤ) (Multiplicative.ofAdd 1)) = z.val := by
  simp [groupLikeEquivHopfCharacters, monoidAlgebraBialgHomEquiv,
    MonoidAlgebra.liftGroupLikeBialgHom]

/-- Spec of the coordinate Hopf algebra, as a bundled group scheme. -/
abbrev affineHopfGroupScheme : Grp (Over (Spec (CommRingCat.of R))) :=
  (hopfSpec (CommRingCat.of R)).obj (.op (CommHopfAlgCat.of R A))

/-- The multiplicative group over an affine base. -/
abbrev multiplicativeGroupScheme : Grp (Over (Spec (CommRingCat.of R))) :=
  affineHopfGroupScheme R (MultiplicativeGroupCoordinate R)

/-- Full faithfulness of Spec identifies Hopf-algebra characters with actual
group-scheme morphisms to the multiplicative group. -/
def hopfCharactersEquivSchemeCharacters :
    (MultiplicativeGroupCoordinate R →ₐc[R] A) ≃
      (affineHopfGroupScheme R A ⟶ multiplicativeGroupScheme R) :=
  (Equiv.mk
    (fun h => (CommHopfAlgCat.ofHom h).op)
    (fun h => h.unop.hom)
    (fun _ => rfl) (fun _ => rfl)).trans
      (hopfSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv

/-- Group-like units are exactly the characters of an affine group scheme. -/
def groupLikeEquivSchemeCharacters :
    GroupLike R A ≃ (affineHopfGroupScheme R A ⟶ multiplicativeGroupScheme R) :=
  (groupLikeEquivHopfCharacters R A).trans (hopfCharactersEquivSchemeCharacters R A)

end MultiplicativeGroup

variable (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
variable [Algebra R B] [Algebra R S]

/-- The relative Spec adjunction identifies affine scheme points with
algebra homomorphisms over the fixed base ring. -/
def affineSchemePointsEquivAlgHom :
    ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))) ≃
        (B →ₐ[R] S) :=
  ((algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv
    (X := .op (CommAlgCat.of R S)) (Y := .op (CommAlgCat.of R B))).symm.trans <|
    Equiv.mk (fun h => h.unop.hom) (fun h => (CommAlgCat.ofHom h).op)
      (fun _ => rfl) (fun _ => rfl)

@[simp]
theorem affineSchemePointsEquivAlgHom_id :
    affineSchemePointsEquivAlgHom R B B (𝟙 _) = AlgHom.id R B := by
  change ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
    (𝟙 ((algSpec (CommRingCat.of R)).obj (.op (CommAlgCat.of R B))))).unop.hom = _
  rw [Functor.FullyFaithful.preimage_id]
  rfl

/-- The affine point correspondence respects composition with the
contravariance of spectrum. -/
theorem affineSchemePointsEquivAlgHom_comp
    (T : Type u) [CommRing T] [Algebra R T]
    (f : (Spec (CommRingCat.of T)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
    (g : (Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))) :
    affineSchemePointsEquivAlgHom R B T (f ≫ g) =
      (affineSchemePointsEquivAlgHom R S T f).comp
        (affineSchemePointsEquivAlgHom R B S g) := by
  exact congrArg (fun h : Opposite.op (CommAlgCat.of R T) ⟶
      Opposite.op (CommAlgCat.of R B) => h.unop.hom)
    ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage_comp
      (X := .op (CommAlgCat.of R T)) (Y := .op (CommAlgCat.of R S))
      (Z := .op (CommAlgCat.of R B)) f g)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters.Construction
