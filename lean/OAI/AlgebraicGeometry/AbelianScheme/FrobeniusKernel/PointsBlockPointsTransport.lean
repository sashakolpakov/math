import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockHeightIso

/-! # Points Block Points Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockPointsTransport.Construction

noncomputable section

section

/-!
An equivariant native source homomorphism induces maps on the exact
CMPoints character blocks. Their original inclusions and torsion-level
embeddings commute with these maps on every test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable (hf : ∀ a : NumberField.RingOfIntegers E, ρ.map a ≫ f = f ≫ σ.map a)

def l45BlockMap (n : ℕ) (τ : Gal(E/ℚ)) :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ n τ).toGrp :=
  (yonedaGrpFullyFaithful (C := Over S)).preimage
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom ≫
      PointsBlockHeightIso.Construction.l45BlockFunctorMap A B ρ σ f hf (j.localCharacter iota τ) n ≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit B σ n τ).inv)

theorem l45BlockMap_points (n : ℕ) (τ : Gal(E/ℚ)) (T : Over S)
    (x : T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit B σ n τ).hom.app (op T)
      (x ≫ (l45BlockMap j iota hsplit A B ρ σ f hf n τ).hom.hom) =
    (PointsBlockHeightIso.Construction.l45BlockFunctorMap A B ρ σ f hf (j.localCharacter iota τ) n).app (op T)
      ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (op T) x) := by
  have h := (yonedaGrpFullyFaithful (C := Over S)).map_preimage
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom ≫
      PointsBlockHeightIso.Construction.l45BlockFunctorMap A B ρ σ f hf (j.localCharacter iota τ) n ≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit B σ n τ).inv)
  have hc := congrArg (fun α => α ≫ (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit B σ n τ).hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  exact congrArg (fun α => (α.app (op T)).hom x) hc

theorem l45BlockMap_inclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    (l45BlockMap j iota hsplit A B ρ σ f hf n τ).hom.hom ≫
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ n τ =
    CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ ≫ f := by
  have h := congrArg Subtype.val (l45BlockMap_points j iota hsplit A B ρ σ f hf n τ _ (𝟙 _))
  change ((𝟙 _) ≫ (l45BlockMap j iota hsplit A B ρ σ f hf n τ).hom.hom) ≫
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ n τ =
    ((𝟙 _) ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ) ≫ f at h
  simpa only [Category.id_comp] using h

/-- The same source q-torsion subgroup remains the same subgroup when
transported through the embedding into q-squared torsion. -/
theorem l45BlockMap_level (τ : Gal(E/ℚ)) {n m : ℕ} (hnm : n ≤ m) :
    CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ hnm ≫
      l45BlockMap j iota hsplit A B ρ σ f hf m τ =
    l45BlockMap j iota hsplit A B ρ σ f hf n τ ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit B σ τ hnm := by
  have : IsClosedImmersion (CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ m τ).left :=
    PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed B σ _ _
  have : Mono (CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ m τ) := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono (CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ m τ)).mp
  change ((CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom ≫
      (l45BlockMap j iota hsplit A B ρ σ f hf m τ).hom.hom) ≫ _ =
    ((l45BlockMap j iota hsplit A B ρ σ f hf n τ).hom.hom ≫
      (CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit B σ τ hnm).hom.hom) ≫ _
  rw [Category.assoc, l45BlockMap_inclusion, ← Category.assoc,
    CMPointsAt.Construction.l45BlockLevelEmbedding_inclusion, Category.assoc,
    CMPointsAt.Construction.l45BlockLevelEmbedding_inclusion, l45BlockMap_inclusion]

end

/-!
An equivariant bijection on source points restricts to a bijection on
the exact character blocks: both torsion and the scalar character
equations are recovered through injectivity. The comparison then uses
the original native block representations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

section CharacterBlocks

variable {O : Type} [CommRing O] {S : Scheme} {g q : ℕ} [Fact q.Prime]
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable (hf : ∀ a : O, ρ.map a ≫ f = f ≫ σ.map a)
variable (χ : O →+* PadicInt q) (n : ℕ) (T : Over S)

theorem l45BlockPointsMap_bijective
    (hpoints : Function.Bijective (IsMonHom.monoidHom f T)) :
    Function.Bijective (PointsBlockHeightIso.Construction.l45BlockPointsMap A B ρ σ f hf χ n T) := by
  constructor
  · intro x y h
    exact Subtype.ext (hpoints.1 (congrArg Subtype.val h))
  · intro y
    obtain ⟨x, hx⟩ := hpoints.2 y.val
    have hx' : x ≫ f = y.val := hx
    have hxmem : x ∈ PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ n T := by
      refine ⟨?_, fun a => ?_⟩
      · apply hpoints.1
        change (x ^ (q ^ n)) ≫ f = (1 : T ⟶ A.scheme) ≫ f
        rw [MonObj.pow_comp, hx', y.property.1, MonObj.one_comp]
      · apply hpoints.1
        change (x ≫ ρ.map a) ≫ f = (x ^ (PadicInt.toZModPow n (χ a)).val) ≫ f
        rw [Category.assoc, hf a, ← Category.assoc, hx', MonObj.pow_comp, hx']
        exact y.property.2 a
    exact ⟨⟨x, hxmem⟩, Subtype.ext hx'⟩

end CharacterBlocks

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable (hf : ∀ a : NumberField.RingOfIntegers E, ρ.map a ≫ f = f ≫ σ.map a)

theorem l45BlockMap_points_bijective (n : ℕ) (τ : Gal(E/ℚ)) (T : Over S)
    (hpoints : Function.Bijective (IsMonHom.monoidHom f T)) :
    Function.Bijective ((yonedaGrp.map (l45BlockMap j iota hsplit A B ρ σ f hf n τ)).app (op T)) := by
  let u := ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).app (op T)).groupIsoToMulEquiv
  let v := ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit B σ n τ).app (op T)).groupIsoToMulEquiv
  let m := PointsBlockHeightIso.Construction.l45BlockPointsMap A B ρ σ f hf (j.localCharacter iota τ) n T
  have hm := l45BlockPointsMap_bijective A B ρ σ f hf (j.localCharacter iota τ) n T hpoints
  have h : (fun x => x ≫ (l45BlockMap j iota hsplit A B ρ σ f hf n τ).hom.hom) =
      fun x => v.symm (m (u x)) := by
    funext x
    apply v.injective
    exact (l45BlockMap_points j iota hsplit A B ρ σ f hf n τ T x).trans
      (v.apply_symm_apply (m (u x))).symm
  change Function.Bijective (fun x => x ≫ (l45BlockMap j iota hsplit A B ρ σ f hf n τ).hom.hom)
  rw [h]
  exact v.symm.bijective.comp (hm.comp u.bijective)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockPointsTransport.Construction
