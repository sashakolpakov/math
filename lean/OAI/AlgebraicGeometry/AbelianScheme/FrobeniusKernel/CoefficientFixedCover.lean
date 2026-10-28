import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientPreimage
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedGroup
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedTorsionBlockEmbedding
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FinitePresentation

/-! # Coefficient Fixed Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientFixedCover.Construction

noncomputable section

/-! The actual coefficient-fixed preimage is a finite flat cover of the
target subgroup and a closed subgroup of the original higher source block. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hσ : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)
  (τ : Gal(E/ℚ)) {J : Grp (Over S)}
  (i : J ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp) (n : ℕ)

local notation "W" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientPreimage.Construction.coefficientPreimage j iota hsplit A B σ f τ i
local notation "e₀" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientPreimage.Construction.coefficientPreimageProjector j iota hsplit A B ρ σ f hσ τ i n
local notation "u₀" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientPreimage.Construction.coefficientPreimageInclusion j iota hsplit A B σ f τ i
local notation "p₀" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientPreimage.Construction.coefficientPreimageProjection j iota hsplit A B σ f τ i

abbrev coefficientFixedGroup : Grp (Over S) := FixedGroupCover.Construction.fixedGroup W e₀
abbrev coefficientFixedInclusion : coefficientFixedGroup j iota hsplit A B ρ σ f hσ τ i n ⟶ Grp.mk A.scheme :=
  FixedGroupCover.Construction.fixedGroupInclusion W e₀ ≫ u₀
abbrev coefficientFixedProjection : coefficientFixedGroup j iota hsplit A B ρ σ f hσ τ i n ⟶ J :=
  FixedGroupCover.Construction.fixedGroupInclusion W e₀ ≫ p₀

local notation "V" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientFixedCover.Construction.coefficientFixedGroup j iota hsplit A B ρ σ f hσ τ i n
local notation "v₀" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientFixedCover.Construction.coefficientFixedInclusion j iota hsplit A B ρ σ f hσ τ i n
local notation "vπ" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientFixedCover.Construction.coefficientFixedProjection j iota hsplit A B ρ σ f hσ τ i n

theorem coefficientFixedInclusion_fixed :
    (v₀).hom.hom ≫ ρ.map (j.projector iota hsplit (n + 1) τ) = (v₀).hom.hom := by
  have hh : FixedGroupCover.Construction.fixedGroupInclusion W e₀ ≫ e₀ = FixedGroupCover.Construction.fixedGroupInclusion W e₀ :=
    (equalizer.condition e₀ (𝟙 W)).trans (Category.comp_id _)
  have h := congrArg (fun t : FixedGroupCover.Construction.fixedGroup W e₀ ⟶ W => t ≫ u₀) hh
  rw [Category.assoc, CoefficientPreimage.Construction.coefficientPreimageProjector_inclusion, ← Category.assoc] at h
  exact congrArg (fun t : FixedGroupCover.Construction.fixedGroup W e₀ ⟶ Grp.mk A.scheme => t.hom.hom) h

variable (hf : ∀ (T : Over S) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ n) = 1)

include hf in
theorem coefficientFixedInclusion_killed : (v₀).hom.hom ^ (q ^ (n + 1)) = 1 := by
  change ((FixedGroupCover.Construction.fixedGroupInclusion W e₀).hom.hom ≫ (u₀).hom.hom) ^ (q ^ (n + 1)) = 1
  rw [← MonObj.comp_pow, CoefficientPreimage.Construction.coefficientPreimage_killed j iota hsplit A B σ f τ i n hf, MonObj.comp_one]

include hf in
theorem coefficientFixedProjection_cover :
    IsFinite (vπ).hom.hom.left ∧ Flat (vπ).hom.hom.left ∧
      LocallyOfFinitePresentation (vπ).hom.hom.left ∧ Surjective (vπ).hom.hom.left := by
  obtain ⟨hfin, hflat, hfp, hsurj⟩ := CoefficientPreimage.Construction.coefficientPreimageProjection_cover j iota hsplit A B σ f τ i
  let : IsFinite (p₀).hom.hom.left := hfin
  let : Flat (p₀).hom.hom.left := hflat
  let : LocallyOfFinitePresentation (p₀).hom.hom.left := hfp
  let : Surjective (p₀).hom.hom.left := hsurj
  exact FixedGroupCover.Construction.fixedGroupProjection_cover W e₀
    (CoefficientPreimage.Construction.coefficientPreimageProjector_idempotent j iota hsplit A B ρ σ f hσ τ i n hf)
    p₀ (CoefficientPreimage.Construction.coefficientPreimageProjector_projection j iota hsplit A B ρ σ f hσ τ i n)

include hf in
theorem coefficientFixedGroup_finite [IsFinite J.X.hom] : IsFinite (V).X.hom := by
  have : IsFinite (W).X.hom := CoefficientPreimage.Construction.coefficientPreimage_finite j iota hsplit A B σ f τ i
  exact FixedGroup.Construction.fixedGroup_finite W e₀
    (CoefficientPreimage.Construction.coefficientPreimageProjector_idempotent j iota hsplit A B ρ σ f hσ τ i n hf)

include hf in
theorem coefficientFixedInclusion_closed [IsFinite J.X.hom] [IsClosedImmersion i.hom.hom.left] :
    IsClosedImmersion (v₀).hom.hom.left := by
  have : IsFinite (W).X.hom := CoefficientPreimage.Construction.coefficientPreimage_finite j iota hsplit A B σ f τ i
  have : IsClosedImmersion (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i).hom.hom.left :=
    CoefficientTargetSubgroup.Construction.coefficientTargetInclusion_closed j iota hsplit B σ τ i
  have : IsClosedImmersion (FixedGroupCover.Construction.fixedGroupInclusion W e₀).hom.hom.left :=
    FixedGroup.Construction.fixedGroupInclusion_closed W e₀
      (CoefficientPreimage.Construction.coefficientPreimageProjector_idempotent j iota hsplit A B ρ σ f hσ τ i n hf)
  exact inferInstanceAs (IsClosedImmersion ((FixedGroupCover.Construction.fixedGroupInclusion W e₀).hom.hom.left ≫ (u₀).hom.hom.left))

include hf in
theorem coefficientFixedGroup_commutative [IsClosedImmersion i.hom.hom.left] :
    IsCommMonObj (V).X := by
  have : IsClosedImmersion (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i).hom.hom.left :=
    CoefficientTargetSubgroup.Construction.coefficientTargetInclusion_closed j iota hsplit B σ τ i
  have : Mono (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i).hom.hom := Over.mono_of_mono_left _
  have : IsCommMonObj (W).X := SubgroupPreimageGeometry.Construction.subgroupPreimage_commutative (Grp.homMk (A := Grp.mk A.scheme) (B := Grp.mk B.scheme) f.hom)
    (CoefficientTargetSubgroup.Construction.coefficientTargetInclusion j iota hsplit B σ τ i)
  exact FixedGroup.Construction.fixedGroup_commutative W e₀
    (CoefficientPreimage.Construction.coefficientPreimageProjector_idempotent j iota hsplit A B ρ σ f hσ τ i n hf)

def coefficientFixedSourceEmbedding : V ⟶
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp :=
  FixedTorsionBlockEmbedding.Construction.fixedTorsionBlockEmbedding j iota hsplit A ρ (n + 1) τ V (v₀).hom.hom
    (coefficientFixedInclusion_killed j iota hsplit A B ρ σ f hσ τ i n hf)
    (coefficientFixedInclusion_fixed j iota hsplit A B ρ σ f hσ τ i n)

theorem coefficientFixedSourceEmbedding_inclusion :
    (coefficientFixedSourceEmbedding j iota hsplit A B ρ σ f hσ τ i n hf).hom.hom ≫
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ = (v₀).hom.hom :=
  FixedTorsionBlockEmbedding.Construction.fixedTorsionBlockLift_inclusion j iota hsplit A ρ (n + 1) τ V (v₀).hom.hom
    (coefficientFixedInclusion_killed j iota hsplit A B ρ σ f hσ τ i n hf)
    (coefficientFixedInclusion_fixed j iota hsplit A B ρ σ f hσ τ i n)

theorem coefficientFixedSourceEmbedding_closed [IsFinite J.X.hom] [IsClosedImmersion i.hom.hom.left] :
    IsClosedImmersion (coefficientFixedSourceEmbedding j iota hsplit A B ρ σ f hσ τ i n hf).hom.hom.left := by
  have : IsClosedImmersion (v₀).hom.hom.left :=
    coefficientFixedInclusion_closed j iota hsplit A B ρ σ f hσ τ i n hf
  exact FixedTorsionBlockEmbedding.Construction.fixedTorsionBlockEmbedding_closed j iota hsplit A ρ (n + 1) τ V (v₀).hom.hom
    (coefficientFixedInclusion_killed j iota hsplit A B ρ σ f hσ τ i n hf)
    (coefficientFixedInclusion_fixed j iota hsplit A B ρ σ f hσ τ i n)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientFixedCover.Construction
