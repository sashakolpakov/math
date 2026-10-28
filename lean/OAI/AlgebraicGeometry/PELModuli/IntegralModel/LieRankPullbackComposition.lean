import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Lie Rank Pullback Composition -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankPullbackComposition

noncomputable section

section

/-! Transport of the actual dual-number Lie eigenspaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k R : Type} [Field k] [CommRing R] {g : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}

/-- A group isomorphism intertwining the action identifies the actual
dual-number points in each eigenspace. -/
def lieEigenpointsIso (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
    (τ : R →+* k) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (h : ∀ a, ρ.map a ≫ e.hom = e.hom ≫ σ.map a) :
    AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ ≃ AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints B σ τ where
  toFun x := ⟨x.val ≫ e.hom, by
    constructor
    · rw [← Category.assoc, x.property.1]
      exact MonObj.one_comp e.hom
    · intro a
      rw [Category.assoc, ← h a, ← Category.assoc, x.property.2 a, Category.assoc]⟩
  invFun y := ⟨y.val ≫ e.inv, by
    constructor
    · rw [← Category.assoc, y.property.1]
      exact MonObj.one_comp e.inv
    · intro a
      apply (cancel_mono e.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← Category.assoc, h a, Category.assoc, Iso.inv_hom_id_assoc]
      exact y.property.2 a⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

theorem hasLieRank_of_iso (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
    (τ : R →+* k) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (h : ∀ a, ρ.map a ≫ e.hom = e.hom ≫ σ.map a)
    (r : ℕ) (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r) : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B σ τ r := by
  obtain ⟨c, hcadd, hcsmul⟩ := hr
  refine ⟨c.trans (lieEigenpointsIso ρ σ τ e h), ?_, ?_⟩
  · intro x y
    change (c (x + y)).val ≫ e.hom = ((c x).val ≫ e.hom) * ((c y).val ≫ e.hom)
    rw [hcadd]
    exact MonObj.mul_comp _ _ e.hom
  · intro a x
    change (c (a • x)).val ≫ e.hom = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k a ≫ (c x).val ≫ e.hom
    rw [hcsmul, Category.assoc]

/-- The canonical composition comparison intertwines pulled-back actions. -/
theorem action_pullbackComp {S T V : Scheme} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (f : T ⟶ S) (h : V ⟶ T) (a : R) :
    (ρ.pullback (h ≫ f)).map a ≫ (A.pullbackCompIso f h).hom =
      (A.pullbackCompIso f h).hom ≫ ((ρ.pullback f).pullback h).map a := by
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom]
  exact (Over.pullbackComp h f).hom.naturality (ρ.map a)

end

/-! The original Lie-rank condition is equivalent across the actual
canonical comparison of iterated and composite geometric pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem hasLieRank_iff_of_iso {k R : Type} [Field k] [CommRing R] {g : ℕ}
    {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
    (τ : R →+* k) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (h : ∀ a, ρ.map a ≫ e.hom = e.hom ≫ σ.map a) (r : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r ↔ AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B σ τ r := by
  have hinv (a : R) : σ.map a ≫ e.inv = e.inv ≫ ρ.map a := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h a,
      Iso.inv_hom_id_assoc]
  let : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ⟨hasLieRank_of_iso ρ σ τ e h r,
    hasLieRank_of_iso σ ρ τ e.symm hinv r⟩

theorem hasLieRank_pullbackComp_iff {R k : Type} [CommRing R] [Field k] {g : ℕ}
    {S T : Scheme.{0}} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (f : T ⟶ S) (p : Spec (.of k) ⟶ T) (τ : R →+* k) (r : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback (p ≫ f)) (ρ.pullback (p ≫ f)) τ r ↔
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank ((A.pullback f).pullback p) ((ρ.pullback f).pullback p) τ r :=
  hasLieRank_iff_of_iso (ρ.pullback (p ≫ f)) ((ρ.pullback f).pullback p) τ
    (A.pullbackCompIso f p) (action_pullbackComp ρ f p) r

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankPullbackComposition
