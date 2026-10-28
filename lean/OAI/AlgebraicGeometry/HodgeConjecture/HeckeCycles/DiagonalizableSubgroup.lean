import OAI.AlgebraicGeometry.Picard.Homomorphisms.CharacterSpan
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Diagonalizable Subgroup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableSubgroup.CM

noncomputable section

/-! A finite commutative closed subgroup of an actual diagonalizable
group is diagonalizable. Surjective Hopf coordinates carry the spanning
characters to spanning characters, retaining the full scheme structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.CharacterSpan.Construction

universe u

theorem monoidAlgebra_character_span (k I : Type u) [Field k] [CommGroup I] :
    Submodule.span k (Set.range (GroupLike.val (R := k) (A := MonoidAlgebra k I))) = ⊤ := by
  have h : Set.range (GroupLike.val (R := k) (A := MonoidAlgebra k I)) =
      {a : MonoidAlgebra k I | IsGroupLikeElem k a} := by
    ext a
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.isGroupLikeElem_val, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  rw [h]
  exact MonoidAlgebra.span_isGroupLikeElem

theorem span_of_surjective (k R T : Type u) [Field k] [CommRing R] [CommRing T]
    [HopfAlgebra k R] [HopfAlgebra k T] (f : R →ₐc[k] T) (hf : Function.Surjective f)
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := R))) = ⊤) :
    Submodule.span k (Set.range (GroupLike.val (R := k) (A := T))) = ⊤ := by
  have h : Submodule.span k (Set.range (f.toLinearMap ∘ GroupLike.val (R := k) (A := R))) = ⊤ := by
    rw [Set.range_comp, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact hf
  apply top_unique
  rw [← h]
  apply Submodule.span_mono
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨f x.val, x.isGroupLikeElem_val.map f⟩, rfl⟩

theorem spanning_presentation_of_closed_embedding (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X] [IsFinite G.X.hom]
    (I : Type u) [CommGroup I]
    (i : G ⟶ (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k I))))
    [IsClosedImmersion i.hom.hom.left] :
    ∃ R : CommHopfAlgCat k, Module.Finite k R ∧
      Nonempty ((hopfSpec (.of k)).obj (.op R) ≅ G) ∧
      Submodule.span k (Set.range (GroupLike.val (R := k) (A := R))) = ⊤ := by
  obtain ⟨R, hR, _, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  let : Module.Finite k R := hR
  let M := CommHopfAlgCat.of k (MonoidAlgebra k I)
  let v := e.hom ≫ i
  let a : M ⟶ R := ((hopfSpec.fullyFaithful (R := .of k)).preimage v).unop
  have ha : (hopfSpec (.of k)).map a.op = v := (hopfSpec.fullyFaithful (R := .of k)).map_preimage v
  let ar : CommRingCat.of M ⟶ CommRingCat.of R := CommRingCat.ofHom a.hom.toAlgHom.toRingHom
  have has : Spec.map ar = v.hom.hom.left := congrArg (fun f => f.hom.hom.left) ha
  have : IsIso e.hom.hom.hom.left :=
    ((Grp.forget (Over (Spec (.of k)))) ⋙ Over.forget (Spec (.of k))).map_isIso e.hom
  have hclosed : IsClosedImmersion v.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left))
  have : IsClosedImmersion (Spec.map ar) := has.symm ▸ hclosed
  have hsurj : Function.Surjective a.hom := by
    have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).surjective.comp
      ((IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ar)).2.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of M)).inv).surjective)
    change Function.Surjective
      ((Scheme.ΓSpecIso (.of M)).inv ≫ (Spec.map ar).appTop ≫ (Scheme.ΓSpecIso (.of R)).hom) at hs
    simpa [ar] using hs
  have hspan := span_of_surjective k M R a.hom hsurj (monoidAlgebra_character_span k I)
  exact ⟨R, hR, ⟨e⟩, hspan⟩

theorem diagonalizable_of_closed_embedding (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X] [IsFinite G.X.hom]
    (I : Type u) [CommGroup I]
    (i : G ⟶ (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k I))))
    [IsClosedImmersion i.hom.hom.left] :
    ∃ R : CommHopfAlgCat k, Module.Finite k R ∧
      Nonempty (G ≅ (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k (GroupLike k R))))) := by
  obtain ⟨R, hR, ⟨e⟩, hspan⟩ := spanning_presentation_of_closed_embedding k G I i
  let : Module.Finite k R := hR
  exact ⟨R, hR, ⟨e.symm ≪≫ (hopfSpec (.of k)).mapIso
    (CommHopfAlgCat.isoMk (Picard.Homomorphisms.CharacterSpan.Construction.characterHopfEquivOfSpan k R hspan)).op⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableSubgroup.CM
