import Mathlib.AlgebraicGeometry.Cover.Directed
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverExistsQuotient
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineBasis

/-! # Free Invariant -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FreeInvariant.Construction.FreeInvariantCover

/-!
# The cover by invariant affine opens with free source

Invariant affine neighborhoods that refine invariant opens form a locally
directed cover. The quotient construction can then be applied to this actual
cover, with its restricted relation and target maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R X : Scheme.{u}} (s t : R ⟶ X)

abbrev Chart := {U : X.Opens // IsAffineOpen U ∧ s ⁻¹ᵁ U = t ⁻¹ᵁ U ∧
  ∃ n : ℕ, letI := (s ∣_ U).appTop.hom.toAlgebra;
    Nonempty (Module.Basis (Fin n) Γ(U.toScheme, ⊤) Γ((s ⁻¹ᵁ U).toScheme, ⊤))}

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
      rw [i.property.2.1, j.property.2.1]
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
    (h : HasAffineRefinements s t) :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f := by
  classical
  let 𝒰 := cover s t h
  let : 𝒰.LocallyDirected := locallyDirected h
  let : ∀ U : 𝒰.I₀, IsAffine (𝒰.X U) := fun U => U.property.1
  choose n b using fun U : Chart s t => U.property.2.2
  exact AffineCoverExistsQuotient.Construction.AffineCoverQuotient.exists_quotient s t e 𝒰
    (fun U => (s ⁻¹ᵁ U.val).toScheme) (fun U => (s ⁻¹ᵁ U.val).ι)
    (fun U => s ∣_ U.val)
    (fun U => (R.isoOfEq U.property.2.1).hom ≫ t ∣_ U.val)
    (fun U => isPullback_morphismRestrict s U.val) (fun U => by
      change (R.isoOfEq U.property.2.1).hom ≫ t ∣_ U.val ≫ U.val.ι = _
      simp)
    n (fun U => (b U).some)

/-- Pointwise free invariant affine charts already supply refinements on
all invariant opens. Both affineness and the basis persist after shrinking. -/
theorem refinements_of_pointwise [IsFinite s] (e : CategoryTheory.EquivalenceRelation s t)
    (h : ∀ x : X, ∃ U : Chart s t, x ∈ U.val) : HasAffineRefinements s t := by
  intro V hV x hx
  obtain ⟨U, hxU⟩ := h x
  let : IsAffine U.val := U.property.1
  obtain ⟨n, ⟨bU⟩⟩ := U.property.2.2
  have hOU : ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ U.val :=
    (Invariant.Construction.InvariantCore.mem_core s t U.val x).mp
      (Invariant.Construction.InvariantCore.le_core s t U.val U.val U.property.2.1 le_rfl hxU)
  have hOV : ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ V :=
    (Invariant.Construction.InvariantCore.mem_core s t V x).mp (Invariant.Construction.InvariantCore.le_core s t V V hV le_rfl hx)
  obtain ⟨D, hD, hOD, hDU, hDV⟩ := AffineNeighborhoodOpen.Construction.AffineNeighborhood.exists_affineOpen_subset X
    {y | Invariant.Construction.InvariantCore.Related s t x y} (Invariant.Construction.InvariantCore.finite_orbit s t x)
    U.val V U.property.1 hOU hOV
  obtain ⟨W, hW, hWD, hWi, hOW⟩ := InvariantAffineEq.Construction.InvariantAffine.exists_invariant_affine e x D hD
    (fun _ hy => hOD hy) (by
      intro E hE hED
      let : IsAffine E := hE
      exact ⟨n, AffineBasis.Construction.AffineBasisTransfer.restrictLE s E U.val (hED.trans hDU) bU⟩)
  let : IsAffine W := hW
  exact ⟨⟨W, hW, hWi, n, AffineBasis.Construction.AffineBasisTransfer.restrictLE s W U.val (hWD.trans hDU) bU⟩,
    hOW x (Invariant.Construction.InvariantCore.related_refl e x), hWD.trans hDV⟩

/-- No directedness or overlap data need be supplied for a pointwise cover
by invariant affine charts with finite-free relation source. -/
theorem exists_quotient_of_pointwise [IsFinite s]
    (e : CategoryTheory.EquivalenceRelation s t)
    (h : ∀ x : X, ∃ U : Chart s t, x ∈ U.val) :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f :=
  exists_quotient e (refinements_of_pointwise e h)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FreeInvariant.Construction.FreeInvariantCover
