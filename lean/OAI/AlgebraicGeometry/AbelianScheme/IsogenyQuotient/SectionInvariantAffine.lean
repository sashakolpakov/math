import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ModulePullbackCoherence
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineEq
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Section Invariant Affine -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionInvariantAffine.Construction

noncomputable section

/-! The invariant core of an affine section locus is affine. The
function used in the norm construction is the ratio of the two actual
pullbacks of the section along the kernel relation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem kernelPair_related_iff {R X Y : Scheme.{u}}
    (q : X ⟶ Y) (s t : R ⟶ X) (hk : IsKernelPair q s t) (x y : X) :
    Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related s t x y ↔ q x = q y := by
  constructor
  · rintro ⟨r, rfl, rfl⟩
    exact congrArg (fun f => f r) hk.w
  · intro h
    obtain ⟨r, hr, hr'⟩ := Scheme.exists_preimage_of_isPullback hk x y h
    exact ⟨r, hr, hr'⟩

set_option backward.isDefEq.respectTransparency false in
theorem sectionInvariantCore_isAffineOpen {R X Y : Scheme.{u}}
    (q : X ⟶ Y) (s t : R ⟶ X) (hk : IsKernelPair q s t) [IsFinite s]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf)
    (hz : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z)) {ι : Type v} [Fintype ι]
    (b : letI := (s ∣_ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z).appTop.hom.toAlgebra
      Module.Basis ι Γ((AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z).toScheme, ⊤)
        Γ((s ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z).toScheme, ⊤)) :
    IsAffineOpen (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core s t (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z)) := by
  let D := AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z
  have : IsAffine D.toScheme := hz
  have : IsAffine (s ⁻¹ᵁ D).toScheme := isAffine_of_isAffineHom (s ∣_ D)
  let j := (s ⁻¹ᵁ D).ι
  let u := j ≫ s
  let v := j ≫ t
  let p := u ≫ q
  have hv : v ≫ q = p := by
    dsimp only [v, p, u]
    rw [Category.assoc, Category.assoc, hk.w]
  have hsource : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection u z) :=
    (congrArg (fun f => IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f z)) (morphismRestrict_ι s D)).mp
      (AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.pullbackSection_through_nonvanishing_isIso z (s ∣_ D))
  let fs := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection u z ≫ (ModulePullbackCoherence.Construction.modulePullbackTo u q p rfl L.sheaf).hom
  let ft := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection v z ≫ (ModulePullbackCoherence.Construction.modulePullbackTo v q p hv L.sheaf).hom
  have : IsIso fs := inferInstanceAs (IsIso
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection u z ≫ (ModulePullbackCoherence.Construction.modulePullbackTo u q p rfl L.sheaf).hom))
  let a := AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate fs ft
  have htarget : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ft = v ⁻¹ᵁ D :=
    (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection v z) (ModulePullbackCoherence.Construction.modulePullbackTo v q p hv L.sheaf)).trans
      (AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange v (L.pullback q) z)
  have ha : (j ≫ t) ⁻¹ᵁ D = (s ⁻¹ᵁ D).toScheme.basicOpen a :=
    htarget.symm.trans (AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate fs ft)
  exact Quotients.FiniteDescent.InvariantAffineEq.Construction.InvariantAffine.isAffineOpen_core
    (hk.equivalenceRelation q s t (pullback.isLimit t s)) D j (s ∣_ D)
    (isPullback_morphismRestrict s D) b a ha

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionInvariantAffine.Construction
