import Mathlib.AlgebraicGeometry.Cover.Directed
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverExistsQuotient

/-! # Invariant Cover Has -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantCoverHas.Construction.InvariantCover

/-!
# The cover by invariant affine opens

Invariant affine neighborhoods that refine invariant opens form a locally
directed cover. The quotient construction can then be applied to this actual
cover, with its restricted relation and target maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R X : Scheme.{u}} (s t : R ⟶ X)

abbrev Chart := {U : X.Opens // IsAffineOpen U ∧ s ⁻¹ᵁ U = t ⁻¹ᵁ U}

/-- Every point of an invariant open has an invariant affine neighborhood
contained in that open. -/
def HasAffineRefinements : Prop :=
  ∀ (V : X.Opens), s ⁻¹ᵁ V = t ⁻¹ᵁ V → ∀ x ∈ V,
    ∃ W : Chart s t, x ∈ W.val ∧ W.val ≤ V

noncomputable abbrev cover (h : HasAffineRefinements s t) : X.OpenCover where
  I₀ := Chart s t
  X U := U.val.toScheme
  f U := U.val.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun _ => inferInstance⟩
    obtain ⟨U, hx, _⟩ := h ⊤ (by simp) x trivial
    exact ⟨U, ⟨x, hx⟩, rfl⟩

variable {s t}

/-- Intersections need only be refined by invariant affine opens; they need
not themselves be affine. -/
@[instance_reducible]
noncomputable def locallyDirected (h : HasAffineRefinements s t) :
    (cover s t h).LocallyDirected where
  trans {i j} hij := X.homOfLE (leOfHom hij)
  trans_id i := by simp
  trans_comp hij hjk := by simp
  w hij := by simp
  directed {i j} z := by
    let p : pullback i.val.ι j.val.ι ⟶ X := pullback.fst _ _ ≫ i.val.ι
    let x : X := p z
    have hx : x ∈ i.val ⊓ j.val := by
      refine ⟨(pullback.fst i.val.ι j.val.ι z).property, ?_⟩
      have he : p z = j.val.ι (pullback.snd i.val.ι j.val.ι z) :=
        congrArg (fun f : pullback i.val.ι j.val.ι ⟶ X => f z) pullback.condition
      change p z ∈ j.val
      rw [he]
      exact (pullback.snd i.val.ι j.val.ι z).property
    have hV : s ⁻¹ᵁ (i.val ⊓ j.val) = t ⁻¹ᵁ (i.val ⊓ j.val) := by
      change (s ⁻¹ᵁ i.val) ⊓ (s ⁻¹ᵁ j.val) = (t ⁻¹ᵁ i.val) ⊓ (t ⁻¹ᵁ j.val)
      rw [i.property.2, j.property.2]
    obtain ⟨k, hxk, hk⟩ := h (i.val ⊓ j.val) hV x hx
    refine ⟨k, homOfLE (hk.trans inf_le_left), homOfLE (hk.trans inf_le_right),
      ⟨x, hxk⟩, ?_⟩
    apply p.isOpenEmbedding.injective
    change (pullback.lift (X.homOfLE (hk.trans inf_le_left))
      (X.homOfLE (hk.trans inf_le_right)) _ ≫ p) (⟨x, hxk⟩ : k.val) = p z
    dsimp only [p]
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    rfl

/-- Produce the quotient from pointwise invariant affine refinement and
bases on the resulting affine source restrictions. -/
theorem exists_quotient [IsFinite s] (e : CategoryTheory.EquivalenceRelation s t)
    (h : HasAffineRefinements s t)
    (hb : ∀ U : Chart s t, ∃ n : ℕ, letI := (s ∣_ U.val).appTop.hom.toAlgebra;
      Nonempty (Module.Basis (Fin n) Γ(U.val.toScheme, ⊤) Γ((s ⁻¹ᵁ U.val).toScheme, ⊤))) :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f := by
  classical
  let 𝒰 := cover s t h
  let : 𝒰.LocallyDirected := locallyDirected h
  let : ∀ U : 𝒰.I₀, IsAffine (𝒰.X U) := fun U => U.property.1
  choose n b using hb
  exact AffineCoverExistsQuotient.Construction.AffineCoverQuotient.exists_quotient s t e 𝒰
    (fun U => (s ⁻¹ᵁ U.val).toScheme) (fun U => (s ⁻¹ᵁ U.val).ι)
    (fun U => s ∣_ U.val)
    (fun U => (R.isoOfEq U.property.2).hom ≫ t ∣_ U.val)
    (fun U => isPullback_morphismRestrict s U.val) (fun U => by
      change (R.isoOfEq U.property.2).hom ≫ t ∣_ U.val ≫ U.val.ι = _
      simp)
    n (fun U => (b U).some)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantCoverHas.Construction.InvariantCover
