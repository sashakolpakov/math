import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicAffineBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicFiltration
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialSheafRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.ModelRestriction

/-! # Logarithmic Le -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Global logarithmic filtration laws and exact étale functoriality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D : β → X.IdealSheafData}

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_comap_etale (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    {Y : Scheme} (g : Y ⟶ X) [Etale g]
    (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (g ≫ f) (fun l => (D l).comap g))
    (J : X.IdealSheafData) (n : ℕ) :
    (A.logarithmicIdeal J n).comap g = B.logarithmicIdeal (J.comap g) n := by
  let : IsLocallyNoetherian Y := B.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ B.openCover
  intro i
  change B.indices at i
  change ((A.logarithmicIdeal J n).comap g).comap (B.map i) =
    (B.logarithmicIdeal (J.comap g) n).comap (B.map i)
  rw [← Scheme.IdealSheafData.comap_comp, B.logarithmicIdeal_restrict]
  apply A.logarithmicIdeal_restrict_etale J n (B.rings i) (B.map i ≫ g)
    (by rw [Category.assoc]; exact B.ground i) (B.equations i)
    (fun l => by rw [Scheme.IdealSheafData.comap_comp]; exact B.component i l)
    (B.model i) (B.affineIdeal (J.comap g) i)
  rw [Scheme.IdealSheafData.comap_comp]
  exact B.affineIdeal_eq (J.comap g) i

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_zero (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) :
    A.logarithmicIdeal J 0 = J := by
  apply ((A.existsUnique_logarithmicIdeal J 0).choose_spec.2 J _).symm
  intro i
  exact A.affineIdeal_eq J i

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_mono (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    {J K : X.IdealSheafData} (hJK : J ≤ K) (n : ℕ) :
    A.logarithmicIdeal J n ≤ A.logarithmicIdeal K n := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_le_of_openCover _ _ A.openCover
  intro i
  change A.indices at i
  change (A.logarithmicIdeal J n).comap (A.map i) ≤ (A.logarithmicIdeal K n).comap (A.map i)
  rw [A.logarithmicIdeal_restrict, A.logarithmicIdeal_restrict]
  apply Global.DifferentialTransform.Construction.affineQuotientKernel_mono
  apply Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_mono
  apply (Affine.KernelOrderEquiv.Construction.affineQuotientKernel_le_iff _ _).mp
  rw [← A.affineIdeal_eq J i, ← A.affineIdeal_eq K i]
  exact Scheme.IdealSheafData.comap_mono (A.map i) hJK

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_monotone_order (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (J : X.IdealSheafData) {n m : ℕ} (hnm : n ≤ m) :
    A.logarithmicIdeal J n ≤ A.logarithmicIdeal J m := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_le_of_openCover _ _ A.openCover
  intro i
  change A.indices at i
  change (A.logarithmicIdeal J n).comap (A.map i) ≤ (A.logarithmicIdeal J m).comap (A.map i)
  rw [A.logarithmicIdeal_restrict, A.logarithmicIdeal_restrict]
  exact Global.DifferentialTransform.Construction.affineQuotientKernel_mono
    (LogarithmicFiltration.Construction.iteratedRelativeLogarithmicDifferentialIdeal_monotone_order ℂ (A.equations i) (A.affineIdeal J i) hnm)

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.le_logarithmicIdeal (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ) :
    J ≤ A.logarithmicIdeal J n := by
  have h := A.logarithmicIdeal_monotone_order J (Nat.zero_le n)
  rwa [A.logarithmicIdeal_zero] at h

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_top (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (n : ℕ) :
    A.logarithmicIdeal ⊤ n = ⊤ := top_le_iff.mp (A.le_logarithmicIdeal ⊤ n)

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_component (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (l : β) (n : ℕ) :
    A.logarithmicIdeal (D l) n = D l := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ A.openCover
  intro i
  change A.indices at i
  change (A.logarithmicIdeal (D l) n).comap (A.map i) = (D l).comap (A.map i)
  rw [A.logarithmicIdeal_restrict, A.component]
  have he : A.affineIdeal (D l) i = Ideal.span {A.equations i l} := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← A.affineIdeal_eq, A.component]
  rw [he, LogarithmicFiltration.Construction.iteratedRelativeLogarithmicDifferentialIdeal_component]

end

section

/-! The global logarithmic filtration lies in the ordinary filtration and equals it for an empty boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D : β → X.IdealSheafData}

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.ambient_smooth (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) : Smooth f := by
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) A.openCover
  intro i
  change A.indices at i
  change Smooth (A.map i ≫ f)
  rw [A.ground i]
  let : Algebra.Smooth ℂ (A.rings i) := (A.model i).smooth
  exact inferInstanceAs (Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (A.rings i)))

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.ordinaryIdeal_restrict [Smooth f] (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (J : X.IdealSheafData) (n : ℕ) (i : A.indices) :
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap (A.map i) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (A.affineIdeal J i) n) := by
  let : Algebra.Smooth ℂ (A.rings i) := (A.model i).smooth
  rw [Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open, A.affineIdeal_eq]
  exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (A.map i ≫ f) _ (A.ground i) _ n).trans
    (ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel (A.rings i) (A.affineIdeal J i) n)

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_le_ordinary [Smooth f] (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (J : X.IdealSheafData) (n : ℕ) : A.logarithmicIdeal J n ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_le_of_openCover _ _ A.openCover
  intro i
  change A.indices at i
  change (A.logarithmicIdeal J n).comap (A.map i) ≤ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap (A.map i)
  rw [A.logarithmicIdeal_restrict, A.ordinaryIdeal_restrict]
  exact Global.DifferentialTransform.Construction.affineQuotientKernel_mono
    (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_le_relative ℂ (A.equations i) (A.affineIdeal J i) n)

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_empty [Smooth f] [IsEmpty β] (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (J : X.IdealSheafData) (n : ℕ) : A.logarithmicIdeal J n = Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ A.openCover
  intro i
  change A.indices at i
  change (A.logarithmicIdeal J n).comap (A.map i) = (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap (A.map i)
  rw [A.logarithmicIdeal_restrict, A.ordinaryIdeal_restrict, Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_empty]

end

/-! Finite selected boundary histories retain their original global affine coordinate models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} {D : β → X.IdealSheafData}

def GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.reindex (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (e : γ ↪ β) :
    GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f (fun j => D (e j)) where
  indices := A.indices
  finite := A.finite
  rings := A.rings
  algebra := A.algebra
  map := A.map
  isOpenImmersion := A.isOpenImmersion
  quasiCompact := A.quasiCompact
  ground := A.ground
  cover := A.cover
  equations i j := A.equations i (e j)
  component i j := A.component i (e j)
  model i := (A.model i).reindex e

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.reindex_affineIdeal (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (e : γ ↪ β)
    (J : X.IdealSheafData) (i : A.indices) : (A.reindex e).affineIdeal J i = A.affineIdeal J i := rfl

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.reindex_logarithmicIdeal_restrict (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (e : γ ↪ β)
    (J : X.IdealSheafData) (n : ℕ) (i : A.indices) :
    ((A.reindex e).logarithmicIdeal J n).comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel
      (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ (fun j => A.equations i (e j)) (A.affineIdeal J i) n) :=
  (A.reindex e).logarithmicIdeal_restrict J n i

end

end OAI.AlgebraicGeometry.Resolution.Blowups
