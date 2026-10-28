import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.MapDetection
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness

/-! # Polarization Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationCancellation.Construction

noncomputable section

/-! The native polarization pullback is injective on group maps over
Noetherian bases, using geometric cancellation without dropping nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_polarizationPullback_injective
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (m₁ m₂ : B.scheme ⟶ DB.abelian.scheme) [IsMonHom m₁] [IsMonHom m₂]
    (hm : f.hom ≫ m₁ ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
      f.hom ≫ m₂ ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB) : m₁ = m₂ := by
  apply MapDetection.Construction.noetherian_pointed_map_eq_of_geometric_baseChanges B.scheme DB.abelian.scheme
    m₁ m₂ (IsMonHom.one_hom _) (IsMonHom.one_hom _)
  intro K _ _ s
  let F := Over.pullback s
  have : IsReduced (B.pullback s).scheme.left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field (B.pullback s).scheme.hom
  have : ConnectedSpace (B.pullback s).scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (B.pullback s).scheme.hom
  have : EffectiveEpi (f.pullback s).hom := Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_over_of_fpqc (f.pullback s).hom
  have : IsFinite (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (f.pullback s).hom (DA.pullback s) (DB.pullback s)).left :=
    FrobeniusKernel.IsogenyPolarizationUniqueness.Construction.isogeny_dualMap_finite (f.pullback s) (DA.pullback s) (DB.pullback s)
  apply FrobeniusKernel.FiniteCancellation.Construction.polarizationPullback_injective (f.pullback s).hom
    (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (f.pullback s).hom (DA.pullback s) (DB.pullback s)) (F.map m₁) (F.map m₂)
  have h := congrArg F.map hm
  simp only [F.map_comp] at h
  have hd := FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange s f.hom DA DB
  change F.map (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB) =
    FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (f.pullback s).hom (DA.pullback s) (DB.pullback s) at hd
  rw [hd] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationCancellation.Construction
