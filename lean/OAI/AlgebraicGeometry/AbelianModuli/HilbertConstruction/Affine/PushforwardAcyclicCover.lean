import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardAllCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionPushforward
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity
import Mathlib.SetTheory.Cardinal.Order

/-! # Pushforward Acyclic Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardAcyclicCover

noncomputable section

/-! An affine direct image is acyclic on any family of opens whose inverse images are affine. The target opens themselves need not be affine. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}} [Y.IsSeparated]
variable (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent]

theorem affinePushforward_cohomology_vanish (n : ℕ)
    (hM : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M n)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((Scheme.Modules.pushforward f).obj M) n) := by
  classical
  let : LinearOrder Y.affineOpens := IsWellOrder.linearOrder (WellOrderingRel (α := Y.affineOpens))
  exact PushforwardAllCohomology.affineCover_pushforward_allCohomology_vanish f (RingHom.id Γ(Y, ⊤)) M
    (fun U : Y.affineOpens => U.1) (iSup_affineOpens_eq_top Y) (fun U => U.2) n hM

theorem affinePushforward_restricted_cohomology_vanish (V : Y.Opens) (n : ℕ)
    (hM : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict (f ⁻¹ᵁ V).ι) n)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      (((Scheme.Modules.pushforward f).obj M).restrict V.ι) n) := by
  have : V.toScheme.IsSeparated :=
    ⟨by rw [← terminal.comp_from V.ι]; infer_instance⟩
  have : IsAffineHom (f ∣_ V) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (isPullback_morphismRestrict f V).flip inferInstance
  let e := Open.RestrictionPushforward.restrictPushforwardIsoOfIsPullbackApp f (f ∣_ V) (f ⁻¹ᵁ V).ι V.ι
    (isPullback_morphismRestrict f V) M
  have h := affinePushforward_cohomology_vanish (f ∣_ V) (M.restrict (f ⁻¹ᵁ V).ι) n hM
  let eH := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor V.toScheme n).mapIso e
  have hi : Function.Injective eH.hom :=
    (AddCommGrpCat.mono_iff_injective eH.hom).mp inferInstance
  exact ⟨fun x y => hi (h.elim _ _)⟩

theorem affinePushforward_affine_preimage_intersections_acyclic
    {ι : Type u} (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (f ⁻¹ᵁ U i)) :
    Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj M)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  intro p i q
  let V : Y.Opens := ∏ᶜ fun k : Fin (p + 1) => U (i k)
  have hV : IsAffineOpen (f ⁻¹ᵁ V) := by
    dsimp only [V]
    rw [CoefficientCech.PushforwardFactors.preimageCechIntersection]
    exact CechIntersections.affine_cechIntersection (fun i => f ⁻¹ᵁ U i) hU p i
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV
  change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
    (((Scheme.Modules.pushforward f).obj M).restrict V.ι) (q + 1))
  exact affinePushforward_restricted_cohomology_vanish f M V (q + 1)
    (ZariskiVanishing.ZariskiCohomology.moduleAffineHSucc_subsingleton (M.restrict (f ⁻¹ᵁ V).ι) q)

theorem affinePushforward_inverseImage_cover_acyclic
    {S : Scheme.{u}} (a : Y ⟶ S) [IsAffineHom (f ≫ a)]
    {ι : Type u} (U : ι → S.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => a ⁻¹ᵁ U i)
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj M)) := by
  apply affinePushforward_affine_preimage_intersections_acyclic f M
  intro i
  change IsAffineOpen ((f ≫ a) ⁻¹ᵁ U i)
  exact (hU i).preimage (f ≫ a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardAcyclicCover
