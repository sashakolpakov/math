import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct

/-! # Coprime Orthogonal Represented -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalRepresented

noncomputable section

/-! The full orthogonal is represented by the Lagrangian factor times the coprime kernel factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct

variable {S : Scheme.{u}} {H K D : Over S} [GrpObj K] [GrpObj D]
  (e : ∀ T : Over S, (T ⟶ K ⊗ D) →* (T ⟶ K ⊗ D) →* Γ(T.left, ⊤)ˣ)
  (n m : ℕ) (hnm : n.Coprime m)
  (hK : ∀ (T : Over S) (x : T ⟶ K), x ^ n = 1)
  (hD : ∀ (T : Over S) (x : T ⟶ D), x ^ m = 1)
  (i : H ⟶ K) (hi : NaturalPairingOrthogonal.SelfAnnihilating i (CoprimeOrthogonalProduct.firstPairing e))

include hnm hK hD hi

/-- The product of actual subgroup schemes represents the full orthogonal image. -/
theorem orthogonal_iff_product_image {T : Over S} (y : T ⟶ K ⊗ D) :
    y ∈ NaturalPairingOrthogonal.orthogonal (i ≫ CoprimeOrthogonalProduct.first) e T ↔ ∃ z : T ⟶ H ⊗ D, z ≫ (i ⊗ₘ 𝟙 D) = y := by
  rw [CoprimeOrthogonalProduct.orthogonal_of_selfAnnihilating e n m hnm hK hD i hi]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨lift k (y ≫ snd K D), ?_⟩
    apply CartesianMonoidalCategory.hom_ext <;> simp [hk]
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ fst H D, ?_⟩
    have hh := congrArg (fun a => a ≫ fst K D) hz
    simpa only [Category.assoc, tensorHom_fst] using hh

omit hnm hK hD hi in
/-- The actual orthogonal subfunctor on all test schemes. -/
def orthogonalPresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj T := NaturalPairingOrthogonal.orthogonal (i ≫ CoprimeOrthogonalProduct.first) e T.unop
  map f := ↾(fun y => ⟨f.unop ≫ y.val, NaturalPairingOrthogonal.orthogonal_baseChange _ _ f.unop y.val y.property⟩)
  map_id T := by
    apply ConcreteCategory.ext_apply
    intro y
    apply Subtype.ext
    exact Category.id_comp y.val
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    intro y
    apply Subtype.ext
    exact Category.assoc _ _ y.val

variable [Mono i]

omit hnm hK hD hi [GrpObj K] [GrpObj D] in
/-- The product inclusion is a monomorphism whenever the original subgroup inclusion is. -/
theorem productInclusion_mono : Mono (i ⊗ₘ 𝟙 D) := by
  constructor
  intro T x y h
  apply CartesianMonoidalCategory.hom_ext
  · apply (cancel_mono i).mp
    have hh := congrArg (fun z => z ≫ fst K D) h
    simpa only [Category.assoc, tensorHom_fst] using hh
  · have hh := congrArg (fun z => z ≫ snd K D) h
    simpa only [Category.assoc, tensorHom_snd, Category.comp_id] using hh

/-- Every orthogonal test point comes uniquely from the actual subgroup product. -/
def pointsEquiv (T : Over S) : (T ⟶ H ⊗ D) ≃ (orthogonalPresheaf e i).obj (op T) := by
  let f : (T ⟶ H ⊗ D) → (orthogonalPresheaf e i).obj (op T) :=
    fun z => ⟨z ≫ (i ⊗ₘ 𝟙 D), (orthogonal_iff_product_image e n m hnm hK hD i hi _).mpr ⟨z, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have : Mono (i ⊗ₘ 𝟙 D) := productInclusion_mono (D := D) i
    exact (cancel_mono (i ⊗ₘ 𝟙 D)).mp (congrArg Subtype.val h)
  · intro y
    obtain ⟨z, hz⟩ := (orthogonal_iff_product_image e n m hnm hK hD i hi y.val).mp y.property
    exact ⟨z, Subtype.ext hz⟩

/-- This is a representation of the complete orthogonal presheaf, including nonreduced test schemes. -/
def representableBy : (orthogonalPresheaf e i).RepresentableBy (H ⊗ D) where
  homEquiv := pointsEquiv e n m hnm hK hD i hi _
  homEquiv_comp a x := by
    apply Subtype.ext
    exact Category.assoc a x (i ⊗ₘ 𝟙 D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalRepresented
